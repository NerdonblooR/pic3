from z3 import *
import heapq
import threading
import boto3
import json
import concurrent.futures
import math


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
                inv = f;
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

def partition_bad_state(h2t, partition_num):
    partitioner = fd_solver()
    good_solver = fd_solver()
    partitioner.add(h2t.goal)
    good_solver.add(Not(h2t.goal))
    bad_states = []
    # partition the bad state
    while sat == partitioner.check():
        m = partitioner.model()
        cube = project_var(m, h2t.x0) + project_var(m, h2t.inputs)
        # good_solver.check(cube)
        # assert (good_solver.check(cube) == unsat)
        # core = good_solver.unsat_core()
        partitioner.add(Not(And(cube)))
        bad_states.append(And(cube))

    batch_size = int(math.ceil(float(len(bad_states))/float(partition_num)))
    subgoals = []
    batch = []
    count = 0
    for bad in bad_states:
        count += 1
        batch.append(bad)
        if count == batch_size and count > 1:
            subgoals.append(str(Or(batch)))
            count = 0
            batch = 0
    if len(batch) > 0:
        if len(batch) > 1:
            subgoals.append(str(Or(batch)))
        else:
            subgoals.append(str(batch[0]))

    return subgoals

#test lambda expression
def invoke_lambda_function(h2t, goal):
    input_list = map(lambda x: str(x), h2t.inputs)
    xs_list = map(lambda x: str(x), h2t.xs)
    xns_list = map(lambda x: str(x), h2t.xns)
    event = {}
    event['init'] = str(h2t.init)
    event['trans'] = str(h2t.goal)
    event['goal'] = str(goal)
    event['inputs'] = " ".join(input_list)
    event['xs'] = " ".join(xs_list)
    event['xns'] = " ".join(xns_list)
    client = boto3.client('lambda')
    response = client.invoke(
        FunctionName='pic3lambda',
        InvocationType='Event',
        LogType='Tail',
        Payload=json.dumps(event)
    )
    return response["message"]


def test(file):
    h2t = Horn2Transitions()
    h2t.parse(file)
    subgoals = partition_bad_state(h2t)
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(subgoals)) as executor:
        term = True
        ret = 'SAT'
        inv_reached = 0
        future_lambda = {executor.submit(invoke_lambda_function, h2t, subgoal): subgoal for subgoal in subgoals}
        while term:
            completed_future = concurrent.futures.as_completed(future_lambda, timeout=1)
            for future in completed_future:
                del future_lambda[future]
                subgoal = future_lambda[future]
                try:
                    response = future.result()
                except Exception as exc:
                    print('%r generated an exception: %s' % (subgoal, exc))
                else:
                    if response == 'Inv':
                        inv_reached += 1
                        if len(subgoal) == inv_reached:
                            ret = 'UNSAT'
                            break
                    elif response == 'cex':
                        term = False
                        break
                    else:
                        #bound reached resubmit another job
                        #add future to future lambda
                        break
        return ret

if __name__ == '__main__':
    # test("data/horn1.smt2")
    # test("data/horn2.smt2")
    # test("data/horn3.smt2")
    test("data/horn4.smt2")
    #test("data/horn5.smt2")
    #test("data/horn6.smt2") # takes long time to finish
