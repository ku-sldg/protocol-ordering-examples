# Kuhn's Algorithm - Maximum Bipartite Matching

# Find a valid map for preceq A B in polynomial time

# Returns (True, f) where f is an injective, label-respecting map from pi A to pi B,
# or returns (False, S) where S is a Hall violator
def match(order, A, B):
    n, k = len(A.pi), len(B.pi)
    g = [[to for to, b in enumerate(B.pi) if order.le(A.tagged[a], B.tagged[b])] for a in A.pi]
    mt = [-1] * k
    used = [False] * n

    def try_kuhn(v):
        if used[v]:
            return False
        used[v] = True
        for to in g[v]:
            if mt[to] == -1 or try_kuhn(mt[to]):
                mt[to] = v
                return True
        return False

    for v in range(n):
        used = [False] * n
        if not try_kuhn(v):
            return (False, [A.pi[u] for u in range(n) if used[u]])
    return (True, sorted((A.pi[mt[i]], B.pi[i]) for i in range(k) if mt[i] != -1))