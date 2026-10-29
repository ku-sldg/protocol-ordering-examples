import os

from handleInput import fail
from kuhn import match

# 
# Basic Coq Terms
#

# [a, b] => a :: b :: nil
def coq_list(items):
    return ' :: '.join(list(items) + ['nil'])

# (P1,) => P1
# (P2, P3) => (P1 ++ P2)
def coq_app(P):
    return P[0] if len(P) == 1 else '(%s)' % ' ++ '.join(P)

# ((T1,), (T2,)) => (T1 :: T2 :: nil)
def coq_traces(M):
    return '(%s)' % coq_list(coq_app(P) for P in M)

# (P2, P3) => P2_app_P3
def ident_set(P):
    return '_app_'.join(P)

# ((T1,) (T2,)) => T1_T2
def ident_traces(M):
    return '_'.join(ident_set(P) for P in M)

# [t1, t2] => apply Forall_cons; [t1|]; apply Forall_cons; [t2|]; apply Forall_nil
def chain(tactics):
    return ''.join('apply Forall_cons; [%s|]; ' % t for t in tactics) + 'apply Forall_nil'

def bool_coq(b):
    return 'true' if b else 'false'


#
# Lemmas and Proofs
#

class Prover:

    def __init__(self, protocols):
        self.protocols = protocols
        self.preceq_cache = {}      # (Order.name, A.qualname, B.qualname) => (holds, witness)
        self.leqs_cache = {}        # (leq|tleq|tstar, Order.name, P, Q) => (holds, lemma name)
        self.leqs_lemmas = []       # Coq source for lemmas proving/disproving leq, tleq, or tstar

    def preceq(self, O, A, B):
        key = (O.name, A.qualname, B.qualname)
        if key not in self.preceq_cache:
            self.preceq_cache[key] = match(O, A, B)
        return self.preceq_cache[key]

    def emit(self, key, holds, name, lines):
        lines.append('Qed.')
        self.leqs_lemmas.append('\n'.join(lines))
        self.leqs_cache[key] = (holds, name)
        return self.leqs_cache[key]
 
    def leq(self, O, P, Q):
        key = ('leq', O.name, P, Q)
        if key in self.leqs_cache:
            return self.leqs_cache[key]
        As, Bs = self.protocols.graphs(P), self.protocols.graphs(Q)
        steps = []
        failing_graph = None
        for B in Bs:
            for n, A in enumerate(As):
                holds, witness = self.preceq(O, A, B)
                if holds:
                    f = '(%s : list (nat * nat))' % coq_list('(%d,%d)' % ab for ab in witness)
                    steps.append('by_map %s %s %d %s' % (O.dec, A.qualname, n, f))
                    break
            else:
                failing_graph = B
                break
        holds = failing_graph is None
        name = '%s_%s_%s_vs_%s' % ('leq' if holds else 'nleq', O.name, ident_set(P), ident_set(Q))
        stmt = 'set_ordering.leq %s %s %s' % (O.rel, coq_app(P), coq_app(Q))
        if holds:
            # leq_intro: 
            # unfold Q to its list of graphs, then
            # prove exists A, In A P /\ preceq A B for each B
            lines = ['Lemma %s : %s.' % (name, stmt),
                     'Proof.',
                     '    apply (leq_intro _ _ _ (%s)); [reflexivity|].' % coq_list(g.qualname for g in Bs)]
            lines += ['    apply Forall_cons; [%s|].' % s for s in steps]
        else:
            # not_leq_intro: 
            # name the graph B of Q (by position) that nothing reaches, 
            # unfold P to its list of graphs, then 
            # prove ~ preceq A B for each A with its Hall violator
            B = failing_graph
            lines = ['Lemma %s : ~ %s.' % (name, stmt),
                     'Proof.',
                     '    apply (not_leq_intro _ _ (%s) _ %s); [in_at %d | reflexivity |].' % (
                         coq_list(g.qualname for g in As), B.qualname, Bs.index(B))]
            for A in As:
                S = self.preceq(O, A, B)[1]
                lines.append('    apply Forall_cons; [by_hall %s %s %s (%s : list nat)|].' % (
                    O.dec, A.qualname, B.qualname, coq_list(str(a) for a in S)))
        lines.append('    apply Forall_nil.')
        return self.emit(key, holds, name, lines)

    def tleq(self, O, M, N):
        key = ('tleq', O.name, M, N)
        if key in self.leqs_cache:
            return self.leqs_cache[key]

        def partner(X, Ys, below):
            for n, Y in enumerate(Ys):
                holds, name = self.leq(O, Y, X) if below else self.leq(O, X, Y)
                if holds:
                    return 'hnf; exists %s; split; [in_at %d | exact %s]' % (coq_app(Y), n, name)
            return None

        n_partners = [partner(Q, M, True) for Q in N]
        m_partners = [partner(P, N, False) for P in M]
        holds = None not in n_partners and None not in m_partners
        name = '%s_%s_%s_vs_%s' % ('tleq' if holds else 'ntleq', O.name, ident_traces(M), ident_traces(N))
        stmt = 'tleq %s %s %s' % (O.rel, coq_traces(M), coq_traces(N))
        if holds:
            # tleq_intro
            lines = ['Lemma %s : %s.' % (name, stmt),
                     'Proof.',
                     '    apply (tleq_intro _ _ %s _ %s); [reflexivity | reflexivity | |].' % (
                         coq_traces(M), coq_traces(N)),
                     '    - ' + chain(n_partners) + '.',
                     '    - ' + chain(m_partners) + '.']
        elif None in n_partners:
            # not_tleq_intro1
            k = n_partners.index(None)
            lines = ['Lemma %s : ~ %s.' % (name, stmt),
                     'Proof.',
                     '    apply (not_tleq_intro1 _ _ %s _ %s); [in_at %d | reflexivity |].' % (
                         coq_traces(M), coq_app(N[k]), k),
                     '    ' + chain('exact ' + self.leq(O, A, N[k])[1] for A in M) + '.']
        else:
            # not_tleq_intro2
            k = m_partners.index(None)
            lines = ['Lemma %s : ~ %s.' % (name, stmt),
                     'Proof.',
                     '    apply (not_tleq_intro2 _ _ _ %s %s); [in_at %d | reflexivity |].' % (
                         coq_traces(N), coq_app(M[k]), k),
                     '    ' + chain('exact ' + self.leq(O, M[k], B)[1] for B in N) + '.']
        return self.emit(key, holds, name, lines)

    def tstar(self, O, M, N):
        key = ('tstar', O.name, M, N)
        if key in self.leqs_cache:
            return self.leqs_cache[key]
        
        failing_pair = next(((i, j) for i, P in enumerate(M) for j, Q in enumerate(N)
                    if not self.leq(O, P, Q)[0]), None)
        holds = failing_pair is None
        name = '%s_%s_%s_vs_%s' % ('tstar' if holds else 'ntstar', O.name, ident_traces(M), ident_traces(N))
        stmt = 'tstar %s %s %s' % (O.rel, coq_traces(M), coq_traces(N))
        if holds:
            # tstar_intro
            rows = [chain(['exact ' + self.leq(O, A, B)[1] for B in N]) for A in M]
            lines = ['Lemma %s : %s.' % (name, stmt),
                     'Proof.',
                     '    apply (tstar_intro _ _ %s _ %s); [reflexivity | reflexivity | discriminate | discriminate |].' % (
                         coq_traces(M), coq_traces(N)),
                     '    ' + chain(rows) + '.']
        else:
            # not_tstar_intro
            i, j = failing_pair
            lines = ['Lemma %s : ~ %s.' % (name, stmt),
                     'Proof.',
                     '    apply (not_tstar_intro _ _ _ %s %s); [in_at %d | in_at %d | exact %s].' % (
                         coq_app(M[i]), coq_app(N[j]), i, j, self.leq(O, M[i], N[j])[1])]
        return self.emit(key, holds, name, lines)

    def order(self, O, P, Q):
        pq_holds, pq_name = self.leq(O, P, Q)
        qp_holds, qp_name = self.leq(O, Q, P)
        verdict = {(True, True): 'equiv', 
                   (True, False): 'leq',
                   (False, True): 'geq', 
                   (False, False): 'incomparable'}[(pq_holds, qp_holds)]
        return verdict, ('apply (order_%s_intro _ %s %s\n'
                         '        %s %s);\n'
                         '    [exact %s | exact %s].' % (verdict, O.dec, O.refl, O.antisym, O.trans, pq_name, qp_name))

    def torder(self, O, M, N):
        mn_holds, mn_name = self.tleq(O, M, N)
        nm_holds, nm_name = self.tleq(O, N, M)

        def star(Xs, Ys):
            holds, name = self.tstar(O, Xs, Ys)
            if holds:
                return holds, 'intros _; exact %s | discriminate' % name
            return holds, 'discriminate | intros _; exact %s' % name

        if mn_holds and nm_holds:
            # torder_equiv_intro: 
            # Check tstar in both directions
            mn_star_holds, mn_star_name = star(M, N)
            nm_star_holds, nm_star_name = star(N, M)
            return '(equiv, %s)' % bool_coq(mn_star_holds and nm_star_holds), \
                'apply (torder_equiv_intro _ %s _ _ %s %s); [exact %s | exact %s | %s | %s].' % (
                    O.dec, bool_coq(mn_star_holds), bool_coq(nm_star_holds), mn_name, nm_name, mn_star_name, nm_star_name)      
        if mn_holds or nm_holds:
            # torder_leq_intro or torder_geq_intro: 
            # Check tstar from lower to upper
            v = 'leq' if mn_holds else 'geq'
            star_holds, star_name = star(M, N) if mn_holds else star(N, M)
            return '(%s, %s)' % (v, bool_coq(star_holds)), \
                'apply (torder_%s_intro _ %s _ _ %s); [exact %s | exact %s | %s].' % (
                    v, O.dec, bool_coq(star_holds), mn_name, nm_name, star_name)
        # torder_incomparable_intro
        return '(incomparable, false)', \
            'apply (torder_incomparable_intro _ %s); [exact %s | exact %s].' % (O.dec, mn_name, nm_name)


# ---------------------------------------------------------------------------
# Full Coq File

class OrderingFile:

    def __init__(self, prover):
        self.prover = prover
        self.lemmas = []                # Coq source for leq, tleq, and tstar helper lemmas
        self.body = []                  # Coq source for definitions and verdict lemmas
        self.protocol_imports = []      # Protocols to import
        self.names = set()              # Names of aliases and verdict lemmas
        self.traces = False             # Whether any pair compares traces

    def claim(self, name):
        if name in self.names:
            fail('%s is defined twice' % name)
        self.names.add(name)

    def import_protocols(self, names):
        self.protocol_imports += [m for m in dict.fromkeys(names) if m not in self.protocol_imports]

    def add_alias(self, name, side):
        self.claim(name)
        self.import_protocols(sum(side.value, ()) if side.kind == 'trace' else side.value)
        self.body.append('Definition %s := %s.' % (name, side.coq))

    def add(self, O, L, R, name=None):
        name = name or '%s_%s_vs_%s' % (O.name, L.ident, R.ident)
        self.claim(name)
        if L.kind == 'trace':
            self.traces = True
            fn, (verdict, tactic) = 'torder_fix', self.prover.torder(O, L.value, R.value)
            used_names = sum(L.value + R.value, ())
        else:
            fn, (verdict, tactic) = 'order_fix', self.prover.order(O, L.value, R.value)
            used_names = L.value + R.value
        self.import_protocols(used_names)
        self.lemmas += self.prover.leqs_lemmas
        self.prover.leqs_lemmas = []
        stmt = '@%s _ _ %s %s %s = %s' % (fn, O.dec, L.arg(), R.arg(), verdict)
        self.body.append('Lemma %s : %s.\nProof.\n    %s\nQed.' % (name, stmt, tactic))

    def header(self, imports=()):
        head = ['(* Generated by scripts/writeOrderProofs.py *)',
                '',
                'Require Import Coq.Lists.List.',
                '',
                'Require Import AttestationProtocolOrdering.attackgraph_ordering.',
                'Require Import AttestationProtocolOrdering.set_ordering.']
        if self.traces:
            head.append('Require Import AttestationProtocolOrdering.trace_ordering.')
        head.append('Require Import AttestationProtocolOrdering.set_relationship.')
        if self.traces:
            head.append('Require Import AttestationProtocolOrdering.trace_relationship.')
        head += ['Require Import AttestationProtocolOrdering.make_adversary_ordering.',
                 '',
                 'Require Import ProtocolOrderingExamples.components.',
                 'Require Import ProtocolOrderingExamples.advOrder.']
        head += [''] + ['Require Import ProtocolOrderingExamples.%s.' % m for m in self.protocol_imports]
        if imports:
            head += [''] + ['Require Import ProtocolOrderingExamples.%s.' % m for m in imports]
        return '\n'.join(head)

    def write(self, out, lemmas_out):
        with open(lemmas_out, 'w') as f:
            f.write(self.header() + '\n\n' + '\n\n'.join(self.lemmas) + '\n')
        lemmas_module = os.path.splitext(os.path.basename(lemmas_out))[0]
        with open(out, 'w') as f:
            f.write(self.header([lemmas_module]) + '\n\n' + '\n\n'.join(self.body) + '\n')

