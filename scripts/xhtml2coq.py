import sys
from bs4 import BeautifulSoup

def validName(s):
    for c in s:
        if c.isalpha() or c.isdigit() or c == '_':
            return True
    return False



if len(sys.argv) == 3 :
    if validName(sys.argv[1]) :
        with open(sys.argv[2] + '/' + sys.argv[1] + '_graphs.xhtml', 'r') as f:
            contents = f.read()
        soup = BeautifulSoup(contents, "html.parser")

        allNodes = []
        allEdges = []
        for graph in soup.find_all('svg') :

            nodes = []
            for node in graph.find_all(class_='node') :
                event = node.title.text
                headSplit = node.text.replace('\n','').replace(event,'').split('(',1)
                bodySplit = headSplit[1].rstrip(')').split(', ')

                eventNat = event.lstrip('n')
                if eventNat.isdigit() :
                    if headSplit[0] == 'cor' or headSplit[0] == 'rep' :
                        if len(bodySplit) == 2 :
                            label = [headSplit[0], bodySplit[1]]
                            nodes.append((eventNat,label))
                        else :
                            sys.stderr.write('Invalid number of event arguments')
                            sys.stderr.write('Expects two')
                            sys.exit()
                    elif headSplit[0] == 'msp' :
                        if len(bodySplit) == 5:
                            label = [headSplit[0], bodySplit[1], bodySplit[3]]
                            nodes.append((eventNat,label))
                        else :
                            sys.stderr.write('Invalid number of event arguments')
                            sys.stderr.write('Expects five')
                            sys.exit()
                    else :
                        sys.stderr.write('Invalid event type')
                        sys.stderr.write('Expects cor, rep, or msp')
                        sys.exit()
                else :
                    sys.stderr.write('Invalid event name')
                    sys.stderr.write('Expects natural number')
                    sys.exit()
            allNodes.append(nodes)

            edges = []
            for edge in graph.find_all(class_='edge') :
                edgeSplit = edge.title.text.split('->')
                if len(edgeSplit) == 2 :
                    edgeNat = (edgeSplit[0].lstrip('n'), edgeSplit[1].lstrip('n'))
                    if edgeNat[0].isdigit() and edgeNat[1].isdigit() :
                        edges.append(edgeNat)
                    else :
                        sys.stderr.write('Invalid event names')
                        sys.stderr.write('Expects natural numbers')
                        sys.exit()
                else :
                    sys.stderr.write('Invalid edge format')
                    sys.stderr.write('Expects -> symbol separator')
                    sys.exit()
            allEdges.append(edges)



        if len(allNodes) == len(allEdges) :
            with open(sys.argv[2] + '/' + sys.argv[1] + '.v', 'w') as f :
                f.write('Require Import AttestationProtocolOrdering.attackgraph.\n')
                f.write('Require Import ProtocolOrderingExamples.components.\n')
                f.write('\n')

                for i in range(len(allNodes)):
                    f.write('Definition A' + str(i) + ' : attackgraph components := \n')
                    f.write('{|\n')

                    f.write('\tevent := \n')
                    f.write('\t\tnat ;\n')

                    f.write('\tedges :=\n')
                    f.write('\t\t')
                    for edge in allEdges[i]:
                        f.write('(' + edge[0] + ',' + edge[1] + ')')
                        f.write(' :: ')
                    f.write('nil ;\n')

                    f.write('\tlabel := fun ev =>\n')
                    f.write('\t\tmatch ev with\n')
                    for node in allNodes[i]:
                        f.write('\t\t| ' + node[0] + ' => ')
                        if len(node[1]) == 2:
                            f.write('inr (' + node[1][0] + ' _ ' + node[1][1] + ')\n')
                        elif len(node[1]) == 3:
                            f.write('inl (' + node[1][0] + ' _ ' + node[1][1] + ' ' + node[1][2] + ')\n')
                    f.write('\t\t| _ => inl (ms _)\n')
                    f.write('\t\tend ;\n')

                    f.write('\teqDec_event := \n')
                    f.write('\t\tltac:(decide equality) ;\n')

                    f.write('\teqDec_component := \n')
                    f.write('\t\teqDec_components\n')

                    f.write('|}.\n\n')

                f.write('Definition ' + sys.argv[1] + ' : list (attackgraph components) := \n')
                f.write('\t')
                for i in range(len(allNodes)):
                    f.write('A' + str(i) + ' :: ')
                f.write('nil.\n')
        else :
            sys.stderr.write('Invalid set of nodes or edges')
            sys.stderr.write('Expects one of each for every attackgraph')
            sys.exit()
    else :
        sys.stderr.write('Invalid command line argument')
        sys.stderr.write('Expects string containing alphanumeric characters or underscores')
        sys.exit()
else :
    sys.stderr.write('Invalid number of command line arguments')
    sys.stderr.write('Expects one')
    sys.exit()
