# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction -I spec -I correctness
EC_FN      ?= -ec xmss_keypair_jazz -ec xmss_sign_jazz -ec xmss_sign_open_jazz
EC_FLAGS   ?= -pragmas Proofs:weak
 
JASMIN    ?= jasminc
JASMIN2EC ?= jasmin2ec
JFLAGS    ?= -nowarning ${JADDFLAGS}
JINCLUDE  ?= -I XMSS:../ref-jasmin/ -I Stdlib:../ref-jasmin/stdlib

JASMIN_SRC := ../ref-jasmin
TEST_SRC   := ../test

JPP          := ../submodules/jasmin-preprocessor/jpp
PREPROCESSOR := ../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

default: extract typecheck_spec check_proofs typecheck_extraction
all: clean distclean extract typecheck_spec check_proofs typecheck_extraction
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

extraction/XMSS_IMPL.ec: | extraction/ common/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jazz
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jazz $(@:.ec=.jazz)
	$(JASMIN2EC) $(@:.ec=.jazz) --output-array common/ > $@
	-$(RM) extraction/XMSS_IMPL.jazz

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck_spec check_proofs typecheck_extraction typecheck_xmss_spec typecheck_xmss_mt_spec
typecheck_xmss_spec:
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/BaseW.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/LTree.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Types.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/WOTS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_PRF.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_TreeHash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss/XMSS_Types.ec

typecheck_xmss_mt_spec:
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/BaseW.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/LTree.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Types.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/WOTS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_PRF.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_TreeHash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/xmss_mt/XMSS_MT_Types.ec


typecheck_spec: typecheck_xmss_spec typecheck_xmss_mt_spec

typecheck_extraction: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $<


check_proofs: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Repr.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Utils.ec
	# $(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Termination.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Utils.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Conditions.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Mem.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Correctness_Hash.ec
	# $(EASYCRYPT) $(EC_INCLUDE) correctness/Correctness_Wots.ec
	# $(EASYCRYPT) $(EC_INCLUDE) correctness/Correctness_XMSS.ec

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	-$(RM) -r *.eco
	-$(RM) -r *~ 
	-$(RM) -r \#*\#
	-$(RM) -r spec/xmss/*.eco
	-$(RM) -r spec/xmss/*~ 
	-$(RM) -r spec/xmss/\#*\#
	-$(RM) -r spec/xmss_mt/*.eco
	-$(RM) -r spec/xmss_mt/*~ 
	-$(RM) -r spec/xmss_mt/\#*\#
	-$(RM) -r correctness/*.eco
	-$(RM) -r correctness/*~ 
	-$(RM) -r correctness/\#*\#


.PHONY: distclean
distclean:	
	-$(RM) -r extraction/XMSS_IMPL.ec common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@


common/:
	mkdir -p $@
