# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction

JASMIN ?= jasminc

JASMIN_SRC := ../ref-jasmin
TEST_SRC   := ../test

default: extract typecheck
extract: extraction/xmss_impl.ec

# --------------------------------------------------------------------------------------------------

# NOTE: __copy_subtree_addr missing

extraction/xmss_impl.ec: | extraction/
	make -C $(TEST_SRC)/wots/ bin/test_wots_xmss-sha2_10_256.jpp
	cp $(TEST_SRC)/wots/bin/test_wots_xmss-sha2_10_256.jpp $(@:.ec=.jinc)
	$(JASMIN) -ec __set_layer_addr \
	          -ec __set_tree_addr \
			  -ec __set_type \
			  -ec __set_key_and_mask \
			  -ec __set_ots_addr \
			  -ec __set_chain_addr \
			  -ec __set_hash_addr \
			  -ec __set_ltree_addr \
			  -ec __set_tree_height \
			  -ec __set_tree_index \
			  -ec _zero_address \
			  -ec __wots_pkgen \
			  -ec __wots_sign \
			  -ec __wots_pk_from_sig -oec $@ $(@:.ec=.jinc)

extraction/xmss.ec: extraction/
	touch $@ # TODO:

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck
typecheck: extract
	$(EASYCRYPT) $(EC_INCLUDE) Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) Primitives.ec
	$(EASYCRYPT) $(EC_INCLUDE) Wots.ec
	$(EASYCRYPT) $(EC_INCLUDE) XMSS.ec

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	rm -rf *.eco
	rm -rf *~ 
	rm -rf \#*\#

.PHONY: distclean
distclean:	
	rm -rf extraction/
	rm -rf Array*.ec WArray*.ec

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@