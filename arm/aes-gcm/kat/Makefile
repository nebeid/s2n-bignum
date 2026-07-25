# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#
# Phase-0 KAT gate for the AES-256-GCM whole-blocks DECRYPT main-loop proof.
# Host must be aarch64 (the frozen .o objects run natively).
#
#   make          build + run the differential KAT gate
#   make run      alias for the default
#   make clean    remove build artifacts
#
# The two objects under test live one directory up and are FROZEN (do not
# rebuild them): aesv8_gcm_8x_dec_256_wb.o (target) and aesv8_gcm_8x_dec_256.o
# (trusted differential reference).

CC      ?= gcc
CFLAGS  ?= -O2 -Wall -Wextra -std=c11
AESDIR   = ..

WB_OBJ   = $(AESDIR)/aesv8_gcm_8x_dec_256_wb.o
SIB_OBJ  = $(AESDIR)/aesv8_gcm_8x_dec_256.o

.PHONY: all run clean
all: run

kat_wb_dec: kat_wb_dec.c $(WB_OBJ) $(SIB_OBJ)
	$(CC) $(CFLAGS) -o $@ kat_wb_dec.c $(WB_OBJ) $(SIB_OBJ)

run: kat_wb_dec
	./kat_wb_dec

clean:
	rm -f kat_wb_dec
