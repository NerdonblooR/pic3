from z3 import *
import heapq
import threading
import boto3
import json
import concurrent.futures
import math
import time
import random
import re


# Simplistic (and fragile) converter from
# a class of Horn clauses corresponding to
# a transition system into a transition system
# representation as <init, trans, goal>
# It assumes it is given three Horn clauses
# of the form:
#  init(x) => Invariant(x)
#  Invariant(x) and trans(x,x') => Invariant(x')
#  Invariant(x) and goal(x) => Goal(x)
# where Invariant and Goal are uninterpreted predicates

class Horn2Transitions:
    def __init__(self):
        self.trans = True
        self.init = True
        self.inputs = []
        self.goal = True
        self.index = 0

    def parse(self, file):
        fp = Fixedpoint()
        goals = fp.parse_file(file)
        for r in fp.get_rules():
            if not is_quantifier(r):
                continue
            b = r.body()
            if not is_implies(b):
                continue
            f = b.arg(0)
            g = b.arg(1)
            if self.is_goal(f, g):
                continue
            if self.is_transition(f, g):
                continue
            if self.is_init(f, g):
                continue

    def is_pred(self, p, name):
        return is_app(p) and p.decl().name() == name

    def is_goal(self, body, head):
        if not self.is_pred(head, "Goal"):
            return False
        pred, inv = self.is_body(body)
        if pred is None:
            return False
        self.goal = self.subst_vars("x", inv, pred)
        self.goal = self.subst_vars("i", self.goal, self.goal)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
        return True

    def is_body(self, body):
        if not is_and(body):
            return None, None
        fmls = [f for f in body.children() if self.is_inv(f) is None]
        inv = None
        for f in body.children():
            if self.is_inv(f) is not None:
                inv = f
                break
        return And(fmls), inv

    def is_inv(self, f):
        if self.is_pred(f, "Invariant"):
            return f
        return None

    def is_transition(self, body, head):
        pred, inv0 = self.is_body(body)
        if pred is None:
            return False
        inv1 = self.is_inv(head)
        if inv1 is None:
            return False
        pred = self.subst_vars("x", inv0, pred)
        self.xs = self.vars
        pred = self.subst_vars("xn", inv1, pred)
        self.xns = self.vars
        pred = self.subst_vars("i", pred, pred)
        self.inputs += self.vars
        self.inputs = list(set(self.inputs))
        self.trans = pred
        return True

    def is_init(self, body, head):
        for f in body.children():
            if self.is_inv(f) is not None:
                return False
        inv = self.is_inv(head)
        if inv is None:
            return False
        self.init = self.subst_vars("x", inv, body)
        return True

    def subst_vars(self, prefix, inv, fml):
        subst = self.mk_subst(prefix, inv)
        self.vars = [v for (k, v) in subst]
        return substitute(fml, subst)

    def mk_subst(self, prefix, inv):
        self.index = 0
        if self.is_inv(inv) is not None:
            return [(f, self.mk_bool(prefix)) for f in inv.children()]
        else:
            vars = self.get_vars(inv)
            return [(f, self.mk_bool(prefix)) for f in vars]

    def mk_bool(self, prefix):
        self.index += 1
        return Bool("%s%d" % (prefix, self.index))

    def get_vars(self, f, rs=[]):
        if is_var(f):
            return z3util.vset(rs + [f], str)
        else:
            for f_ in f.children():
                rs = self.get_vars(f_, rs)
            return z3util.vset(rs, str)


# Produce a finite domain solver.
# The theory QF_FD covers bit-vector formulas
# and pseudo-Boolean constraints.
# By default cardinality and pseudo-Boolean
# constraints are converted to clauses. To override
# this default for cardinality constraints
# we set sat.cardinality.solver to True

def fd_solver():
    s = SolverFor("QF_FD")
    s.set("sat.cardinality.solver", True)
    return s


# negate, avoid double negation
def negate(f):
    if is_not(f):
        return f.arg(0)
    else:
        return Not(f)


def cube2clause(cube):
    return Or([negate(f) for f in cube])


class State:
    def __init__(self, s):
        self.R = set([])
        self.solver = s

    def add(self, clause):
        if clause not in self.R:
            self.R |= {clause}
            self.solver.add(clause)


class Goal:
    def __init__(self, cube, parent, level):
        self.level = level
        self.cube = cube
        self.parent = parent


def is_seq(f):
    return isinstance(f, list) or isinstance(f, tuple) or isinstance(f, AstVector)


# Check if the initial state is bad
def check_disjoint(a, b):
    s = fd_solver()
    s.add(a)
    s.add(b)
    return unsat == s.check()


# Remove clauses that are subsumed
def prune(R):
    removed = set([])
    s = fd_solver()
    for f1 in R:
        s.push()
        for f2 in R:
            if f2 not in removed:
                s.add(Not(f2) if f1.eq(f2) else f2)
        if s.check() == unsat:
            removed |= {f1}
        s.pop()
    return R - removed


def value2literal(m, x):
    value = m.eval(x)
    if is_true(value):
        return x
    if is_false(value):
        return Not(x)
    return None


def values2literals(m, xs):
    p = [value2literal(m, x) for x in xs]
    return [x for x in p if x is not None]


def project_var(m, vars):
    return values2literals(m, vars)


'''
Partition bad states by retrieving bad state assignment
'''


def partition_bad_state(h2t, partition_num):
    partitioner = fd_solver()
    good_solver = fd_solver()
    partitioner.add(h2t.goal)
    good_solver.add(Not(h2t.goal))
    bad_states = []
    # partition the bad state
    while sat == partitioner.check():
        m = partitioner.model()
        cube = project_var(m, h2t.xs) + project_var(m, h2t.inputs)
        # good_solver.check(cube)
        # assert (good_solver.check(cube) == unsat)
        # core = good_solver.unsat_core()
        partitioner.add(Not(And(cube)))
        bad_states.append(And(cube))

    batch_size = int(math.ceil(float(len(bad_states)) / float(partition_num)))
    subgoals = []
    batch = []
    print len(bad_states)
    print batch_size
    count = 0
    for bad in bad_states:
        count += 1
        batch.append(bad)
        if count == batch_size:
            if len(batch) > 1:
                subgoals.append(" ".join(str(Or(batch)).split()))
            else:
                subgoals.append(" ".join(str(batch[0]).split()))
            count = 0
            batch = []

    if len(batch):
        if len(batch) > 1:
            subgoals.append(" ".join(str(Or(batch)).split()))
        else:
            subgoals.append(" ".join(str(batch[0]).split()))
    return subgoals


def retrieve_shared_variables(init, bad):
    init_var = set(re.findall(r'x[0-9]+', init))
    bad_var = set(re.findall(r'x[0-9]+', bad))
    ret = list(init_var & bad_var)
    return ret


def enumerate_all_assignment(num_var):
    ret = [[]]
    for i in range(num_var):
        new_ret = []
        for elem in ret:
            elem_cpy_0 = elem[:]
            elem_cpy_1 = elem[:]
            elem_cpy_0.append(0)
            elem_cpy_1.append(1)
            new_ret.append(elem_cpy_0)
            new_ret.append(elem_cpy_1)
        ret = new_ret
    return ret


'''
Another way to partition the bad states
'''


def partition_bad_state_shared_variable(init, goal, partition_exp):
    init_str = str(init)
    goal_str = str(goal)
    shared_vars = retrieve_shared_variables(init_str, goal_str)

    if len(shared_vars) > partition_exp:
        shared_vars = random.sample(shared_vars, partition_exp)

    print shared_vars

    var_num = len(shared_vars)
    all_assign = enumerate_all_assignment(var_num)

    subgoals = []
    for assign in all_assign:
        sub_goal_list = []
        for i in range(var_num):
            var = Bool(shared_vars[i])
            if assign[i]:
                sub_goal_list.append(var)
            else:
                sub_goal_list.append(Not(var))
        subgoals.append(str(And(goal, And(sub_goal_list))))

    return subgoals


"""
invoke a lambda funciton
"""
# test lambda expression
def invoke_lambda_function(id, model, model_vars, goal, mode, re_sub):
    session = boto3.session.Session()
    client = session.client('lambda')
    event = {'init': str(model[0]), 'trans': str(model[1]), 'goal': str(goal), 'inputs': " ".join(model_vars[0]),
             'xs': " ".join(model_vars[1]), 'xns': " ".join(model_vars[2]), 'r': 0, 'backward': 0, 'id': id}

    # backward_pdr
    if mode == 'b':
        # generate reverse pdr by:
        # 1. xs in init and goal to xn
        # 2. flip goal and inputs
        event['init'] = str(goal).replace('x', 'xn')
        event['trans'] = str(model[1])
        event['goal'] = str(model[0]).replace('x', 'xn')
        event['inputs'] = " ".join(model_vars[0])
        event['xs'] = " ".join(model_vars[1])
        event['xns'] = " ".join(model_vars[2])
        event['backward'] = 1

    # re-submit if bound of an instance is reached
    if re_sub:
        event['r'] = 1

    response = client.invoke(
        FunctionName='pic3lambda',
        InvocationType='RequestResponse',
        LogType='Tail',
        Payload=json.dumps(event)
    )
    resp = json.loads(response['Payload'].read())
    # print resp
    return resp['message']


def retrieve_completed_task(futures):
    done = []
    for future in futures:
        if future.done():
            done.append(future)
    return done


def test(file):
    h2t = Horn2Transitions()
    h2t.parse(file)
    input_list = map(lambda x: str(x), h2t.inputs)
    xs_list = map(lambda x: str(x), h2t.xs)
    xns_list = map(lambda x: str(x), h2t.xns)
    model_vars = [input_list, xs_list, xns_list]

    init_str = str(h2t.init)
    trans_str = str(h2t.trans)
    model = [init_str, trans_str]

    partition_exp = 2
    sub_goals = partition_bad_state_shared_variable(h2t.init, h2t.goal, partition_exp)
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(sub_goals) * 2) as executor:
        print "Initializing {0} workers: ".format(len(sub_goals) * 2)
        term = True
        ret = 'SAT'
        inv_reached = set()

        # dictionaries for
        lambda_futures = {}
        lambda_modes = {}
        lambda_resub_times = {}
        lambda_id = {}

        count = 0

        for sub_goal in sub_goals:
            f_forward = executor.submit(invoke_lambda_function, count, model[:], model_vars[:], sub_goal, "", 0)
            lambda_id[f_forward] = count
            count += 1
            f_backward = executor.submit(invoke_lambda_function, count, model[:], model_vars[:], sub_goal, "b", 0)
            lambda_id[f_backward] = count
            count += 1

            lambda_futures[f_forward] = sub_goal
            lambda_futures[f_backward] = sub_goal
            lambda_modes[f_forward] = ""
            lambda_modes[f_backward] = "b"
            lambda_resub_times[f_forward] = 0
            lambda_resub_times[f_backward] = 0

        while term:
            completed_future = retrieve_completed_task(lambda_futures)
            print "Waiting for workers to complete..."
            for future in completed_future:
                sub_goal = lambda_futures[future]
                del lambda_futures[future]
                try:
                    response = future.result()
                except Exception as exc:
                    print('%r generated an exception: %s' % ("future[{0}]".format(sub_goal), exc))
                else:
                    if response == 'nondet':
                        # bound reached resubmit another job
                        mode = lambda_modes[future]
                        resub_times = lambda_resub_times[future] + 1
                        task_id = lambda_id[future]

                        del lambda_modes[future]
                        del lambda_resub_times[future]
                        del lambda_id[future]

                        f = executor.submit(invoke_lambda_function, task_id, model[:], model_vars[:], sub_goal, mode,
                                            resub_times)

                        lambda_futures[f] = sub_goal
                        lambda_modes[f] = mode
                        lambda_resub_times[f] = resub_times
                        lambda_id[f] = task_id

                    elif response == 'cex':
                        term = False
                        break
                    else:  # reach an inv
                        print "Worker [sub-goal: {0}] completes\n Invariant:\n {1}".format(sub_goal, response)
                        inv_reached.add(sub_goal)
                        # print subgoal
                        if len(sub_goals) == len(inv_reached):
                            term = False
                            ret = 'UNSAT'
                            break
            time.sleep(1)
        return ret


if __name__ == '__main__':
    # print test("data/horn4.smt2")
    # test("data/horn1.smt2")
    # test("data/horn2.smt2")
    test("data/horn4.smt2")
    #print enumerate_all_assignment(3)
