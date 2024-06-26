# -*- Makefile -*-

# Install jq with sudo apt-get install jq

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction -I spec -I correctness
EC_FN      ?= -ec xmss_keypair_jazz -ec xmss_sign_jazz -ec xmss_sign_open_jazz
EC_FLAGS   ?= -pragmas Proofs:weak
 
JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../ref-jasmin/ -I Stdlib:../ref-jasmin/stdlib

JASMIN_SRC := ../ref-jasmin
TEST_SRC   := ../test

JPP          := ../submodules/jasmin-preprocessor/jpp
PREPROCESSOR := ../submodules/jasmin-preprocessor/preprocessor

JQ_EXISTS := $(shell which jq)

# --------------------------------------------------------------------------------------------------

default: extract typecheck_spec typecheck_proofs typecheck_extraction
all: clean distclean extract typecheck_spec typecheck_proofs typecheck_extraction
extract: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec

# --------------------------------------------------------------------------------------------------

extraction/XMSS_IMPL.ec: | extraction/ common/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jazz
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jazz $(@:.ec=.jazz)
	$(JASMIN) $(JFLAGS) $(EC_FN) -oec $@ $(@:.ec=.jazz)
	mv Array*.ec common/
	mv WArray*.ec common/
	$(RM) extraction/XMSS_IMPL.jazz


extraction/XMSS_IMPL_PP.ec: extraction/XMSS_IMPL.ec | extraction/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jpp
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jpp extraction/tmp.jpp
	$(PREPROCESSOR) -in extraction/tmp.jpp --print_tasks | ./scripts/remove_sha256.py -in $< -out $@
	$(RM) extraction/tmp.jpp


ifdef JQ_EXISTS
.PHONY: extraction_info
extraction_info: extraction/XMSS_IMPL.ec | extraction/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jpp
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jpp extraction/tmp.jpp
	$(PREPROCESSOR) -in extraction/tmp.jpp --print_tasks | jq
	@$(RM) extraction/tmp.jpp
else
.PHONY: extraction_info
extraction_info:
	@echo "extraction_info: jq is not installed." && exit 1
endif

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck_spec typecheck_proofs typecheck_extraction
typecheck_spec: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Primitives.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Wots.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/XMSS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/XMSS_MT_PRF.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Properties.ec


typecheck_extraction: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec
	$(EASYCRYPT) $(EC_INCLUDE) extraction/XMSS_IMPL.ec
	$(EASYCRYPT) $(EC_INCLUDE) extraction/XMSS_IMPL_PP.ec


typecheck_proofs: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Utils.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Conditions.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Mem.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Termination.ec
	# $(EASYCRYPT) $(EC_INCLUDE) correctness/Correctness_Wots.ec
	# $(EASYCRYPT) $(EC_INCLUDE) correctness/Correctness_XMSS.ec

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) -rf *.eco
	$(RM) -rf *~ 
	$(RM) -rf \#*\#


.PHONY: distclean
distclean:	
	$(RM) -rf extraction/XMSS_* common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@


common/:
	mkdir -p $@
