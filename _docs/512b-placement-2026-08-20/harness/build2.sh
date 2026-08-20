#!/bin/bash
# build2.sh <cfgname> <leadpad_bytes> <tag0> ... <tag7>
#   builds bin/<cfgname>, an 8-slot h2 binary.  Slot i gets a copy of
#   obj/<tag_i>.o with its function renamed dec_s<i> and its main-loop marker
#   renamed ml_s<i>.  <leadpad_bytes> bytes of never-executed .text are linked
#   ahead of the whole slot group to shift every kernel's absolute address.
#   Writes bin/<cfgname>.addr with the symbol addresses and alignments.
set -e
cd /tmp/pl
cfg="$1"; lead="$2"; shift 2
tags=("$@")
NV=${#tags[@]}
mkdir -p bin obj

padobj=""
if [ "$lead" != "0" ]; then
  printf '\t.text\n\t.globl padblob_%s\npadblob_%s:\n\t.space %s, 0\n' "$lead" "$lead" "$lead" > obj/pad$lead.S
  as -o obj/pad$lead.o obj/pad$lead.S
  padobj="obj/pad$lead.o"
fi

objs=""
names=""
for i in $(seq 0 $((NV-1))); do
  t=${tags[$i]}
  objcopy --redefine-sym aesv8_gcm_8x_dec_256_wb=dec_s$i \
          --redefine-sym ml_mark=ml_s$i \
          --keep-global-symbol=dec_s$i --keep-global-symbol=ml_s$i \
          obj/$t.o obj/${cfg}_slot$i.o
  objs="$objs obj/${cfg}_slot$i.o"
  names="$names\"$t.s$i\","
done
names=${names%,}

gcc -O2 -DNV=$NV -DSLOTNAMES="$names" -o bin/$cfg h2.c $padobj $objs obj/awslchelp.o

# symbol map: address, and alignment of the function entry and the main loop
{
  echo "# cfg=$cfg leadpad=$lead slots=${tags[*]}"
  printf "%-10s %-16s %-18s %6s %6s %6s\n" slot tag symbol addr16 addr32 addr64
  for i in $(seq 0 $((NV-1))); do
    for s in dec_s$i ml_s$i; do
      a=$(nm bin/$cfg | awk -v s=$s '$3==s{print $1}')
      d=$((16#$a))
      printf "%-10s %-16s %-18s 0x%-14x %4d %4d %4d\n" "$i" "${tags[$i]}" "$s" "$d" $((d%16)) $((d%32)) $((d%64))
    done
    e=$((16#$(nm bin/$cfg | awk -v s=dec_s$i '$3==s{print $1}')))
    m=$((16#$(nm bin/$cfg | awk -v s=ml_s$i '$3==s{print $1}')))
    echo "           ml_offset_in_function=$((m-e))"
  done
} > bin/$cfg.addr
echo "built bin/$cfg  (slots: ${tags[*]}, leadpad=$lead)"
