# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction

JASMIN   ?= jasminc
JFLAGS   ?= -nowarning ${JADDFLAGS}
JINCLUDE ?= -I XMSS:../ref-jasmin/ -I Stdlib:../ref-jasmin/stdlib

JASMIN_SRC := ../ref-jasmin
TEST_SRC   := ../test

JPP          := ../submodules/jasmin-preprocessor/jpp
PREPROCESSOR := ../submodules/jasmin-preprocessor/preprocessor

all: clean distclean extract typecheck_extraction typecheck
default: extract typecheck

extract: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec

# --------------------------------------------------------------------------------------------------

# NOTE: __copy_subtree_addr missing

extraction/XMSS_IMPL.ec: | extraction/ common/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jazz
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jazz $(@:.ec=.jazz)
	$(JASMIN) $(JFLAGS) -ec xmss_keypair_jazz \
	                    -ec xmss_sign_jazz \
						-ec xmss_sign_open_jazz \
						-oec $@ $(@:.ec=.jazz)
	mv Array*.ec common/
	mv WArray*.ec common/
	$(RM) extraction/XMSS_IMPL.jazz

extraction/XMSS_IMPL_PP.ec: extraction/XMSS_IMPL.ec | extraction/
	$(MAKE) -C $(TEST_SRC)/xmss/ clean bin/test_xmss_xmss-sha2_10_256.jpp
	cp $(TEST_SRC)/xmss/bin/test_xmss_xmss-sha2_10_256.jpp extraction/tmp.jpp
	$(PREPROCESSOR) -in extraction/tmp.jpp --print_tasks | ./scripts/remove_sha256.py -in $< -out $@
	$(RM) extraction/tmp.jpp

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck
typecheck: extract
	$(EASYCRYPT) $(EC_INCLUDE) Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) Primitives.ec
	$(EASYCRYPT) $(EC_INCLUDE) Wots.ec
	# $(EASYCRYPT) $(EC_INCLUDE) XMSS.ec
	$(EASYCRYPT) $(EC_INCLUDE) Properties.ec
	$(EASYCRYPT) $(EC_INCLUDE) Correctness.ec

.PHONY: typecheck_extraction
typecheck_extraction: extraction/XMSS_IMPL.ec extraction/XMSS_IMPL_PP.ec
	$(EASYCRYPT) $(EC_INCLUDE) extraction/XMSS_IMPL.ec
	$(EASYCRYPT) $(EC_INCLUDE) extraction/XMSS_IMPL_PP.ec

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	$(RM) -rf *.eco
	$(RM) -rf *~ 
	$(RM) -rf \#*\#

.PHONY: distclean
distclean:	
	$(RM) -rf extraction/ common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@

common/:
	mkdir -p $@
