import os
import sys

from handleInput import fail, read_adv_ordering, read_spec, Protocols, Ordering, Sides
from writeOrderProofs import Prover, OrderingFile


def main():
    if len(sys.argv) != 2:
        fail('usage: python3 genOrdering.py <foldername>')
    exdir = os.path.join('..', sys.argv[1].rstrip('/'))
    spec = os.path.join(exdir, 'myOrdering.spec')
    if not os.path.isfile(spec):
        fail('no %s' % spec)
    items = read_spec(spec)
    if not any(item[0] == 'pair' for item in items):
        return
    adv_text = read_adv_ordering(exdir)

    output = OrderingFile(Prover(Protocols(exdir)))
    sides = Sides()
    orders = {}
    for item in items:
        if item[0] == 'alias':
            _, name, text = item
            output.add_alias(name, sides.define(name, text))
        else:
            _, name, order, lhs, rhs = item
            if order not in orders:
                orders[order] = Ordering(adv_text, order)
            L, R = sides.parse_pair(lhs, rhs)
            output.add(orders[order], L, R, name)
            
    output.write(os.path.join(exdir, 'myOrdering.v'), os.path.join(exdir, 'myOrderingHelper.v'))


if __name__ == '__main__':
    main()
