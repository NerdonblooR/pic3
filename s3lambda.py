from z3 import *
import heapq
import re
import boto3
from boto3.dynamodb.conditions import Key, Attr
import time

BOUND = 10


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


class BoundedIC3:
    def __init__(self, init, trans, goal, x0, inputs, xn, re_sub_times, backward, var_str, task_id):
        self.x0 = x0
        self.inputs = inputs
        self.xn = xn
        self.init = init
        self.bad = goal
        self.trans = trans
        self.min_cube_solver = fd_solver()
        self.min_cube_solver.add(Not(trans))
        self.goals = []
        s = State(fd_solver())
        s.add(init)
        s.solver.add(trans)
        self.states = [s]
        self.s_bad = fd_solver()
        self.s_good = fd_solver()
        self.s_bad.add(self.bad)
        self.s_good.add(Not(self.bad))
        # Add by Hao
        # the bound on the number of frames:
        self.task_id = task_id
        self.resub = re_sub_times
        self.bound = BOUND * (re_sub_times + 1)
        self.backward = backward
        self.var_str = var_str
        self.last_pull = 0

    def next(self, f):
        if is_seq(f):
            return [self.next(f1) for f1 in f]
        return substitute(f, zip(self.x0, self.xn))

    def prev(self, f):
        if is_seq(f):
            return [self.prev(f1) for f1 in f]
        return substitute(f, zip(self.xn, self.x0))

        # add a new frame to states, each state solver contains a new solver that

    # embed a transition
    def add_solver(self):
        s = fd_solver()
        s.add(self.trans)
        self.states += [State(s)]

        # retrive the lemmas of f_i

    def R(self, i):
        return And(self.states[i].R)

    # Check if there are two states next to each other that have the same clauses.
    def is_valid(self):
        i = 1
        while i + 1 < len(self.states):
            if not (self.states[i].R - self.states[i + 1].R):
                return And(prune(self.states[i].R))
            i += 1
        return None

    def value2literal(self, m, x):
        value = m.eval(x)
        if is_true(value):
            return x
        if is_false(value):
            return Not(x)
        return None

    def values2literals(self, m, xs):
        p = [self.value2literal(m, x) for x in xs]
        return [x for x in p if x is not None]

    def project0(self, m):
        return self.values2literals(m, self.x0)

    def projectI(self, m):
        return self.values2literals(m, self.inputs)

    def projectN(self, m):
        return self.values2literals(m, self.xn)

    # Determine if there is a cube for the current state
    # that is potentially reachable.
    def unfold(self):
        core = []
        # add a checkpoint
        self.s_bad.push()
        R = self.R(len(self.states) - 1)
        self.s_bad.add(R)
        is_sat = self.s_bad.check()
        if is_sat == sat:
            m = self.s_bad.model()
            cube = self.project0(m)
            props = cube + self.projectI(m)
            self.s_good.push()
            self.s_good.add(R)
            is_sat2 = self.s_good.check(props)
            assert is_sat2 == unsat
            core = self.s_good.unsat_core()
            core = [c for c in core if c in set(cube)]
            self.s_good.pop()
        self.s_bad.pop()
        return is_sat, core

    # Block a cube by asserting the clause corresponding to its negation
    def block_cube(self, i, cube):
        self.assert_clause(i, cube2clause(cube))

    # Add a clause to levels 0 until i
    def assert_clause(self, i, clause):
        for j in range(i + 1):
            self.states[j].add(clause)

    # minimize cube that is core of Dual solver.
    # this assumes that props & cube => Trans
    def minimize_cube(self, cube, inputs, lits):
        is_sat = self.min_cube_solver.check(lits + [c for c in cube] + [i for i in inputs])
        assert is_sat == unsat
        core = self.min_cube_solver.unsat_core()
        assert core
        return [c for c in core if c in set(cube)]

    # push a goal on a heap
    def push_heap(self, goal):
        heapq.heappush(self.goals, (goal.level, goal))

    # A state s0 and level f0 such that
    # not(s0) is f0-1 inductive
    def ic3_blocked(self, s0, f0):
        self.push_heap(Goal(self.next(s0), None, f0))
        while self.goals:
            f, g = heapq.heappop(self.goals)
            # sys.stdout.write("%d." % f)
            # sys.stdout.flush()
            # Not(g.cube) is f-1 invariant
            if f == 0:
                print("")
                return g
            cube, f, is_sat = self.is_inductive(f, g.cube)
            if is_sat == unsat:
                self.block_cube(f, self.prev(cube))
                # Add by Hao:
                if self.is_true_inductive(cube):
                    # Hao: this is an inductive lemma, share it
                    self.push_lemma(cube2clause(cube))
                if f < f0:
                    self.push_heap(Goal(g.cube, g.parent, f + 1))
            elif is_sat == sat:
                self.push_heap(Goal(cube, g, f - 1))
                self.push_heap(g)
            else:
                return is_sat
        print("")
        return None

    # Rudimentary generalization:
    # If the cube is already unsat with respect to transition relation
    # extract a core (not necessarily minimal)
    # otherwise, just return the cube.
    def generalize(self, cube, f):
        s = self.states[f - 1].solver
        if unsat == s.check(cube):
            core = s.unsat_core()
            if not check_disjoint(self.init, self.prev(And(core))):
                return core, f
        return cube, f

    # Check if the negation of cube is inductive at level f
    def is_inductive(self, f, cube):
        s = self.states[f - 1].solver
        s.push()
        s.add(self.prev(Not(And(cube))))
        is_sat = s.check(cube)
        if is_sat == sat:
            m = s.model()
        s.pop()
        if is_sat == sat:
            cube = self.next(self.minimize_cube(self.project0(m), self.projectI(m), self.projectN(m)))
        elif is_sat == unsat:
            cube, f = self.generalize(cube, f)
        return cube, f, is_sat

    # Check if the negation of cube is inductive relative to true
    def is_true_inductive(self, cube):
        s = fd_solver()
        s.add(self.init)
        s.add(self.trans)
        s.push()
        s.add(self.prev(Not(And(cube))))
        is_sat = s.check(cube)
        return is_sat == unsat

    """
    Checkpoint current state
    """

    def checkpoint(self):
        dynamodb = boto3.resource('dynamodb')
        table = dynamodb.Table('ic3state')
        for i in range(len(self.states)):
            state = self.states[i]
            lemma_count = 0
            for lemma in state.R:
                # generate
                lemma_id = '{0}:{1}'.format(i, lemma_count)
                lemma_count += 1
                response = table.put_item(
                    Item={
                        'task_id': self.task_id,
                        'lemma_id': lemma_id,
                        'lemma': str(lemma)
                    }
                )
                # print response

    """
    Restore from checkpoint
    """

    def restore(self):
        print "restoring"
        dynamodb = boto3.resource('dynamodb')
        table = dynamodb.Table('ic3state')
        previous_bound = self.bound - BOUND

        # construct frames:
        for i in range(previous_bound):
            self.add_solver()

        exec self.var_str

        # get all records associate with my task id
        response = table.scan(
            FilterExpression=Key('task_id').eq(self.task_id)
        )
        # process records
        for i in response['Items']:
            lemma_id = i['lemma_id']
            frame_lemma = lemma_id.split(':')
            frame = int(frame_lemma[0])
            lemma = eval(i['lemma'])
            self.states[frame].add(lemma)

    def pull_lemmas(self):
        dynamodb = boto3.resource('dynamodb')
        table = dynamodb.Table('ic3lemmadb')
        exec self.var_str

        # pull all lemma shared since last pull
        response = table.scan(
            FilterExpression=Attr('task_id').ne(self.task_id) & Key('time_stamp').gt(self.last_pull)
        )

        self.last_pull = int(time.time() * 1000)
        # since all lemmas are inductive, add to all frames
        for i in response['Items']:
            lemma = eval(i['lemma'])
            print lemma
            # add to all frame:
            for state in self.states:
                state.add(lemma)

    def push_lemma(self, lemma):
        dynamodb = boto3.resource('dynamodb')
        table = dynamodb.Table('ic3lemmadb')
        timestamp = int(round(time.time() * 1000))
        id = '{0}.{1}'.format(self.task_id, timestamp)
        response = table.put_item(
            Item={
                'lemma_id': id,
                'time_stamp': timestamp,
                'task_id': self.task_id,
                'lemma': str(lemma)
            }
        )
        # print response

    def run(self):
        if self.resub:
            self.restore()

        if not check_disjoint(self.init, self.bad):
            return "goal is reached in initial state"
        level = self.resub * BOUND
        while True:
            # pull lemmas
            self.pull_lemmas()

            # bound reached
            if level > self.bound:
                self.checkpoint()
                return "nondet"

            inv = self.is_valid()
            if inv is not None:
                return inv
            is_sat, cube = self.unfold()
            if is_sat == unsat:
                level += 1
                print("Unfold %d" % level)
                sys.stdout.flush()
                self.add_solver()
            elif is_sat == sat:
                cex = self.ic3_blocked(cube, level)
                if cex is not None:
                    return cex
            else:
                return is_sat


h2t = Horn2Transitions()
h2t.parse("data/horn4.smt2")

input_list = map(lambda x: str(x), h2t.inputs)
xs_list = map(lambda x: str(x), h2t.xs)
xns_list = map(lambda x: str(x), h2t.xns)

init_str = str(h2t.init)
trans_str = str(h2t.trans)
goal_str = str(h2t.goal)
inputs_str = " ".join(input_list)
xs_str = " ".join(xs_list)
xns_str = " ".join(xns_list)
back_bit = 0
resub_times = 0
task_id = 1

variables = "{0} {1} {2}".format(xs_str, inputs_str, xns_str)
print variables
v_list = variables.split()
print v_list
var_str = "{0} = Bools('{1}')".format(",".join(v_list), " ".join(v_list))
print var_str

exec var_str

xs = Bools(str(xs_str))
inputs = Bools(str(inputs_str))
xns = Bools(str(xns_str))

init = eval(init_str)
goal = eval(goal_str)

trans_str = trans_str.replace("\n", "")
trans_str = re.sub(r'(.*)AtMost\(\((.*)\), ([0-9])\)', r'\1AtMost(\2, \3)', trans_str)
trans = eval(trans_str)

term = False
while not term:
    mp = BoundedIC3(init, trans, goal, xs, inputs, xns, resub_times, back_bit, var_str, task_id)
    result = mp.run()
    if str(result) == "nondet":
        resub_times += 1
    else:
        if isinstance(result, Goal):
            g = result
            print("Trace")
            while g:
                print(g.level, g.cube)
                g = g.parent
            print {'message': 'cex'}

        if isinstance(result, ExprRef):
            print("Invariant:\n%s " % result)
            print {'message': str(result)}
            term = True

        term = True
        print {'message': result}
