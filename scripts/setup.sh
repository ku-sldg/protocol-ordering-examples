#!/bin/bash

exDir="$1"

bash getAllAttacks.sh "${exDir}"
if [[ -f "../${exDir}/myOrdering.spec" ]]; then
  python3 genOrdering.py "${exDir}" || exit 1
fi
python3 genCoqProject.py "${exDir}"