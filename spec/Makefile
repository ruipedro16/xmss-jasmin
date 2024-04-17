# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction

JASMIN ?= jasminc
JFLAGS ?= -nowarning ${JADDFLAGS}

JASMIN_SRC := ../ref-jasmin
TEST_SRC   := ../test

default: extract typecheck
extract: extraction/xmss_impl.ec

# --------------------------------------------------------------------------------------------------

# NOTE: __copy_subtree_addr missing

extraction/xmss_impl.ec: | extraction/ common/
	make -C $(TEST_SRC)/xmss_commons/ clean bin/test_xmss_commons_xmss-sha2_10_256.jpp
	cp $(TEST_SRC)/xmss_commons/bin/test_xmss_commons_xmss-sha2_10_256.jpp $(@:.ec=.jinc)
	$(JASMIN) $(JFLAGS) -ec __set_layer_addr \
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
			  			-ec __wots_pk_from_sig \
						-ec __memcmp -oec $@ $(@:.ec=.jinc)
	mv Array*.ec common/
	mv WArray*.ec common/

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck
typecheck: extract
	$(EASYCRYPT) $(EC_INCLUDE) Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) Primitives.ec
	$(EASYCRYPT) $(EC_INCLUDE) Wots.ec
	$(EASYCRYPT) $(EC_INCLUDE) Properties.ec
	# $(EASYCRYPT) $(EC_INCLUDE) XMSS.ec

# --------------------------------------------------------------------------------------------------

.PHONY: clean
clean:
	rm -rf *.eco
	rm -rf *~ 
	rm -rf \#*\#

.PHONY: distclean
distclean:	
	rm -rf extraction/ common/

# --------------------------------------------------------------------------------------------------

extraction/:
	mkdir -p $@

common/:
	mkdir -p $@
