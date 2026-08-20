#!/bin/bash
K=$HOME/.ssh/ubuntu-m6g-ohio.pem
O="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"
for hc in "3.15.223.40:gv3" "18.222.169.155:gv4" "3.16.157.189:gv5"; do
  h=${hc%%:*}; t=${hc##*:}
  echo "=== $t ($h) ==="
  ssh -i $K $O ubuntu@$h "tail -2 /tmp/pl/run_$t.log; ls /tmp/pl/logs/ | tr '\n' ' '; echo"
done
echo "=== r8g ==="
ssh -o LogLevel=ERROR ec2r8g "tail -2 /tmp/pl/run_r8g.log; ls /tmp/pl/logs/ | tr '\n' ' '; echo"
