#!/bin/bash
K=$HOME/.ssh/ubuntu-m6g-ohio.pem
SSHO="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o ConnectTimeout=15 -o LogLevel=ERROR"
UNPACK='rm -rf /tmp/pl && mkdir -p /tmp/pl && tar xzf /tmp/plstage.tgz -C /tmp/pl && chmod +x /tmp/pl/*.sh && echo unpacked'
for h in 3.15.223.40 18.222.169.155 3.16.157.189; do
  ( scp -q -i $K $SSHO /tmp/plstage.tgz ubuntu@$h:/tmp/ && \
    ssh -i $K $SSHO ubuntu@$h "$UNPACK" && echo "OK $h" ) &
done
( scp -q ec2r8g:/dev/null /dev/null 2>/dev/null; scp -q /tmp/plstage.tgz ec2r8g:/tmp/ && \
  ssh ec2r8g "$UNPACK" && echo "OK ec2r8g" ) &
wait
