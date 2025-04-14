import sys

if len(sys.argv) == 2:
    with open('../_CoqProject', 'w') as f :
        f.write('-Q ' + sys.argv[1] + ' ProtocolOrderingExamples\n')
        f.write('-arg -w -arg -notation-overridden\n')
        f.write('\n')
        f.write(sys.argv[1])