# -*- Makefile -*-

EASYCRYPT  ?= easycrypt
EC_INCLUDE ?= -I common -I extraction

JASMIN ?= jasminc

JASMIN_SRC := ../ref-jasmin

default: extract typecheck
extract: extraction/hash_address.ec

# --------------------------------------------------------------------------------------------------

# NOTE: __copy_subtree_addr missing

extraction/hash_address.ec: $(JASMIN_SRC)/hash_address/hash_address.jinc | extraction/
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
			  -ec _zero_address -oec $@ $<

extraction/xmss.ec: extraction/
	touch $@ # TODO:

# --------------------------------------------------------------------------------------------------

.PHONY: typecheck
typecheck: extract
	$(EASYCRYPT) $(EC_INCLUDE) Notation.ec
	$(EASYCRYPT) $(EC_INCLUDE) Address.ec
	$(EASYCRYPT) $(EC_INCLUDE) Primitives.ec
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