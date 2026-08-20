#!/bin/bash
# fetch.sh [pattern]  -> /tmp/plres/<tag>/
K=$HOME/.ssh/ubuntu-m6g-ohio.pem
O="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"
pat=${1:-'*'}
mkdir -p /tmp/plres
for hc in "3.15.223.40:gv3" "18.222.169.155:gv4" "3.16.157.189:gv5"; do
  h=${hc%%:*}; t=${hc##*:}
  mkdir -p /tmp/plres/$t
  scp -q -i $K $O "ubuntu@$h:/tmp/pl/logs/$pat" /tmp/plres/$t/ 2>/dev/null
  scp -q -i $K $O "ubuntu@$h:/tmp/pl/bin/*.addr" /tmp/plres/$t/ 2>/dev/null
done
mkdir -p /tmp/plres/r8g
scp -q "ec2r8g:/tmp/pl/logs/$pat" /tmp/plres/r8g/ 2>/dev/null
scp -q "ec2r8g:/tmp/pl/bin/*.addr" /tmp/plres/r8g/ 2>/dev/null
ls -la /tmp/plres/*/ | head -60
