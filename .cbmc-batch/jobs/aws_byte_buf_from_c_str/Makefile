include ../Makefile

proofs.goto:
	cd ../../..; \
	goto-cc .cbmc-batch/byte_buf_proofs.c source/byte_buf.c \
	source/array_list.c source/common.c source/error.c -Iinclude/ \
	-I.cbmc-batch/ -o .cbmc-batch/jobs/aws_byte_buf_from_c_str/proofs.goto \
	--function aws_byte_buf_from_c_str_verify
