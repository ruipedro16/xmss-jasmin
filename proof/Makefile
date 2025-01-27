# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction -I spec -I correctness
EC_FLAGS   ?= -timeout 20 $(EC_INCLUDE) ${ECADDFLAGS}

JASMIN    ?= jasminc
JASMIN2EC ?= jasmin2ec
JINCLUDE  ?= -I XMSS:../ref-jasmin/ -I Stdlib:../ref-jasmin/stdlib

TEST_DIR := ../test

JPP          := ../submodules/jasmin-preprocessor/jpp
PREPROCESSOR := ../submodules/jasmin-preprocessor/preprocessor

# --------------------------------------------------------------------------------------------------

default: extract check_spec check_proofs check_extraction
all: clean distclean extract check_spec check_proofs check_extraction
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

$(TEST_DIR)/xmss/bin/test_xmss_xmssmt-sha2_20_2_256.jazz:
	$(MAKE) -C $(TEST_DIR)/xmss/ clean bin/test_xmss_xmssmt-sha2_20_2_256.jazz


extraction/XMSS_IMPL.ec: $(TEST_DIR)/xmss/bin/test_xmss_xmssmt-sha2_20_2_256.jazz | extraction/ common/
	cp $(TEST_DIR)/xmss/bin/test_xmss_xmssmt-sha2_20_2_256.jazz $(@:.ec=.jazz)
	$(JASMIN2EC) $(@:.ec=.jazz) --output-array common/ > $@

# --------------------------------------------------------------------------------------------------

.PHONY: check_spec check_proofs check_extraction check_xmss_spec check_xmss_mt_spec
check_xmss_spec:
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

check_xmss_mt_spec:
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


check_spec: check_xmss_spec check_xmss_mt_spec

check_extraction: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $<

################################### correctness proof ##############################################

# The targets check_c_* are used to check the correctness proof files 
check_c_%: extraction/XMSS_IMPL.ec
	$(EASYCRYPT) $(EC_FLAGS) correctness/$*.ec

CORRECTNESS_PROOF_FILES := $(addprefix check_c_, $(notdir $(basename $(wildcard correctness/*.ec))))

check_correctness_proof: extraction/XMSS_IMPL.ec $(CORRECTNESS_PROOF_FILES)

####################################################################################################

check_xmss_xmssmt_proof: 
	$(EASYCRYPT) $(EC_FLAGS) spec/XMSS_vs_XMSS_MT.ec

check_proofs: check_xmss_xmssmt_proof check_correctness_proof

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
