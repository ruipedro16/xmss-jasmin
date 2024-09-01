# -*- Makefile -*-

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

# --------------------------------------------------------------------------------------------------

default: extract typecheck_spec typecheck_proofs typecheck_extraction
all: clean distclean extract typecheck_spec typecheck_proofs typecheck_extraction
extract: extraction/XMSS_IMPL.ec

# --------------------------------------------------------------------------------------------------

extraction/XMSS_IMPL.ec: | extraction/ common/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jazz
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jazz $(@:.ec=.jazz)
	$(JASMIN) $(JFLAGS) $(EC_FN) -oec $@ $(@:.ec=.jazz)
	mv Array*.ec common/
	mv WArray*.ec common/
	-$(RM) extraction/XMSS_IMPL.jazz

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck_spec typecheck_proofs typecheck_extraction
typecheck_spec: extraction/XMSS_IMPL.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Params.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Types.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Util.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Hash.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Primitives.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/Wots.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/XMSS.ec
	$(EASYCRYPT) $(EC_INCLUDE) spec/XMSS_MT_PRF.ec


typecheck_extraction: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $<


typecheck_proofs: extraction/XMSS_IMPL.ec 
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Repr.ec
	$(EASYCRYPT) $(EC_INCLUDE) $(EC_FLAGS) correctness/Termination.ec
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


.PHONY: distclean
distclean:	
	-$(RM) -r extraction/XMSS_IMPL.ec common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@


common/:
	mkdir -p $@
