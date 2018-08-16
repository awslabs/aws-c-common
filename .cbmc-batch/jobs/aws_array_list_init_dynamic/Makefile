include ../Makefile

proofs.goto:
	cd ../../..; \
	goto-cc .cbmc-batch/array_list_proofs.c source/byte_buf.c \
	source/array_list.c source/common.c source/error.c -Iinclude/ \
	-I.cbmc-batch/ -o .cbmc-batch/jobs/aws_array_list_init_dynamic/proofs.goto \
	--function aws_array_list_init_dynamic_verify
