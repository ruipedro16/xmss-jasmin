require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.

require import Array2 Array3 Array4 Array8 Array11 Array32 Array64 Array67
               Array68 Array96 Array128 Array132 Array136 Array320 Array352
               Array2144.
require import WArray2 WArray4 WArray12 WArray32 WArray44 WArray64 WArray68
               WArray96 WArray128 WArray132 WArray136 WArray256 WArray268
               WArray320 WArray352 WArray2144.

require import XMSS_IMPL.

op Hash_96 : W8.t Array32.t -> W8.t Array96.t -> W8.t Array32.t.
op Hash_128 : W8.t Array32.t -> W8.t Array128.t -> W8.t Array32.t.
op Hash_ptr : W8.t Array32.t -> W64.t -> W64.t -> W8.t Array32.t.

op PRF : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.

module Mp(SC:Syscall_t) = {
  proc __u32_to_bytes (out:W8.t Array4.t, in_0:W32.t) : W8.t Array4.t = {

    in_0 <- BSWAP_32 in_0;
    out <-
    Array4.init
    (WArray4.get8 (WArray4.set32_direct (WArray4.init8 (fun i => (out).[i])) 0 (in_0)));
    return (out);
  }

  proc __ull_to_bytes_2 (out:W8.t Array2.t, in_0:W64.t) : W8.t Array2.t = {
    var aux: int;

    var i:int;

    aux <- (- 1);
    i <- (2 - 1);
    while (aux < i) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- i - 1;
    }
    return (out);
  }

  proc __ull_to_bytes_4 (out:W8.t Array4.t, in_0:W64.t) : W8.t Array4.t = {
    var aux: int;

    var i:int;

    aux <- (- 1);
    i <- (4 - 1);
    while (aux < i) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- i - 1;
    }
    return (out);
  }

  proc __ull_to_bytes_32 (out:W8.t Array32.t, in_0:W64.t) : W8.t Array32.t = {
    var aux: int;

    var i:int;

    aux <- (- 1);
    i <- (32 - 1);
    while (aux < i) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- i - 1;
    }
    return (out);
  }

  proc __bytes_to_ull_4 (in_0:W8.t Array4.t) : W64.t = {

    var result:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    var  _1:bool;

    result <- (W64.of_int 0);
    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 4))) {
      t <- (zeroextu64 in_0.[(W64.to_uint i)]);
      u <- (W64.of_int (4 - 1));
      u <- (u - i);
      (_of_, _cf_, _sf_,  _0, _zf_, u) <- SHL_64 u (W8.of_int 3);
      (_of_, _cf_, _sf_,  _1, _zf_, t) <- SHL_64 t (truncateu8 u);
      result <- (result `|` t);
      i <- (i + (W64.of_int 1));
    }
    return (result);
  }

  proc __bytes_to_ull_ptr (in_ptr:W64.t, inlen:W64.t) : W64.t = {

    var result:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    var  _1:bool;

    result <- (W64.of_int 0);
    i <- (W64.of_int 0);

    while ((i \ult inlen)) {
      t <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (in_ptr + i))));
      u <- inlen;
      u <- (u - (W64.of_int 1));
      u <- (u - i);
      (_of_, _cf_, _sf_,  _0, _zf_, u) <- SHL_64 u (W8.of_int 3);
      (_of_, _cf_, _sf_,  _1, _zf_, t) <- SHL_64 t (truncateu8 u);
      result <- (result `|` t);
      i <- (i + (W64.of_int 1));
    }
    return (result);
  }

  proc __cond_u32_a_below_b_and_a_below_c (a:W32.t, b:W32.t, c:W32.t) : 
  bool = {

    var c3:bool;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var c1:bool;
    var bc1:W8.t;
    var c2:bool;
    var bc2:W8.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;

    (_of_, _cf_, _sf_,  _0, _zf_) <- CMP_32 a b;
    c1 <- (_uLT _of_ _cf_ _sf_ _zf_);
    bc1 <- SETcc c1;
    (_of_, _cf_, _sf_,  _1, _zf_) <- CMP_32 a c;
    c2 <- (_uLT _of_ _cf_ _sf_ _zf_);
    bc2 <- SETcc c2;
    (_of_, _cf_, _sf_,  _2, _zf_) <- TEST_8 bc1 bc2;
    c3 <- (_NEQ _of_ _cf_ _sf_ _zf_);
    return (c3);
  }

  proc __cond_u64_geq_u64_u32_eq_u32 (a:W64.t, b:W64.t, c:W32.t, d:W32.t) : 
  bool = {

    var c3:bool;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var c1:bool;
    var bc1:W8.t;
    var c2:bool;
    var bc2:W8.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;

    (_of_, _cf_, _sf_,  _0, _zf_) <- CMP_64 a b;
    c1 <- (_uGE _of_ _cf_ _sf_ _zf_);
    bc1 <- SETcc c1;
    (_of_, _cf_, _sf_,  _1, _zf_) <- CMP_32 c d;
    c2 <- (_EQ _of_ _cf_ _sf_ _zf_);
    bc2 <- SETcc c2;
    (_of_, _cf_, _sf_,  _2, _zf_) <- TEST_8 bc1 bc2;
    c3 <- (_NEQ _of_ _cf_ _sf_ _zf_);
    return (c3);
  }

  proc __memset_zero_u8_4 (a:W8.t Array4.t) : W8.t Array4.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 4))) {
      a.[(W64.to_uint i)] <- (W8.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }

  proc __memset_u8_128 (a:W8.t Array128.t, value:W8.t) : W8.t Array128.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 128))) {
      a.[(W64.to_uint i)] <- value;
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }

  proc __memset_u8_4 (a:W8.t Array4.t, value:W8.t) : W8.t Array4.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 4))) {
      a.[(W64.to_uint i)] <- value;
      i <- (i + (W64.of_int 1));
    }
    return (a);
  }

  proc __memset_u8_ptr (a_ptr:W64.t, inlen:W64.t, value:W8.t) : unit = {

    var _ptr:W64.t;
    var i:W64.t;

    _ptr <- a_ptr;
    i <- (W64.of_int 0);

    while ((i \ult inlen)) {
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (_ptr + (W64.of_int 0))) (value);
      _ptr <- (_ptr + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return ();
  }

  proc __memcpy_u8u8_128_64 (out:W8.t Array128.t, offset:W64.t,
                             in_0:W8.t Array64.t) : W8.t Array128.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 64))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_32_32 (out:W8.t Array32.t, offset:W64.t,
                            in_0:W8.t Array32.t) : W8.t Array32.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_128_32 (out:W8.t Array128.t, offset:W64.t,
                             in_0:W8.t Array32.t) : W8.t Array128.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_64_64 (out:W8.t Array64.t, offset:W64.t,
                            in_0:W8.t Array64.t) : W8.t Array64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 64))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_96_32 (out:W8.t Array96.t, offset:W64.t,
                            in_0:W8.t Array32.t) : W8.t Array96.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_64_32 (out:W8.t Array64.t, offset:W64.t,
                            in_0:W8.t Array32.t) : W8.t Array64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8_2144_32 (out:W8.t Array2144.t, offset:W64.t,
                              in_0:W8.t Array32.t) : W8.t Array2144.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc _memcpy_u8u8_128_64 (out:W8.t Array128.t, offset:W64.t,
                            in_0:W8.t Array64.t) : W8.t Array128.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_128_64 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8u8_32_32 (out:W8.t Array32.t, offset:W64.t,
                           in_0:W8.t Array32.t) : W8.t Array32.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_32_32 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8u8_128_32 (out:W8.t Array128.t, offset:W64.t,
                            in_0:W8.t Array32.t) : W8.t Array128.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_128_32 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8u8_64_64 (out:W8.t Array64.t, offset:W64.t,
                           in_0:W8.t Array64.t) : W8.t Array64.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_64_64 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8u8_96_32 (out:W8.t Array96.t, offset:W64.t,
                           in_0:W8.t Array32.t) : W8.t Array96.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_96_32 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8u8_64_32 (out:W8.t Array64.t, offset:W64.t,
                           in_0:W8.t Array32.t) : W8.t Array64.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8_64_32 (out, offset, in_0);
    return (out, offset);
  }

  proc _x_memcpy_u8u8_128_64 (out:W8.t Array128.t, offset:W64.t,
                              in_0:W8.t Array64.t) : W8.t Array128.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_128_64 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8_32_32 (out:W8.t Array32.t, offset:W64.t,
                             in_0:W8.t Array32.t) : W8.t Array32.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_32_32 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8_128_32 (out:W8.t Array128.t, offset:W64.t,
                              in_0:W8.t Array32.t) : W8.t Array128.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_128_32 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8_64_64 (out:W8.t Array64.t, offset:W64.t,
                             in_0:W8.t Array64.t) : W8.t Array64.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_64_64 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8_96_32 (out:W8.t Array96.t, offset:W64.t,
                             in_0:W8.t Array32.t) : W8.t Array96.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_96_32 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8_64_32 (out:W8.t Array64.t, offset:W64.t,
                             in_0:W8.t Array32.t) : W8.t Array64.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8_64_32 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc __memcpy_u8u8p_32 (out:W8.t Array32.t, offset:W64.t, in_0:W64.t,
                          inlen:W64.t) : W8.t Array32.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult inlen)) {
      out.[(W64.to_uint offset)] <-
      (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8u8p_64 (out:W8.t Array64.t, offset:W64.t, in_0:W64.t,
                          inlen:W64.t) : W8.t Array64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult inlen)) {
      out.[(W64.to_uint offset)] <-
      (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc _memcpy_u8u8p_32 (out:W8.t Array32.t, offset:W64.t, in_0:W64.t,
                         inlen:W64.t) : W8.t Array32.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8p_32 (out, offset, in_0, inlen);
    return (out, offset);
  }

  proc _memcpy_u8u8p_64 (out:W8.t Array64.t, offset:W64.t, in_0:W64.t,
                         inlen:W64.t) : W8.t Array64.t * W64.t = {

    (out, offset) <@ __memcpy_u8u8p_64 (out, offset, in_0, inlen);
    return (out, offset);
  }

  proc _x_memcpy_u8u8p_32 (out:W8.t Array32.t, offset:W64.t, in_0:W64.t,
                           inlen:W64.t) : W8.t Array32.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8p_32 (out, offset, in_0, inlen);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8u8p_64 (out:W8.t Array64.t, offset:W64.t, in_0:W64.t,
                           inlen:W64.t) : W8.t Array64.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8u8p_64 (out, offset, in_0, inlen);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc __memcpy_u8u8_2_64_2144 (out:W8.t Array64.t, out_offset:W64.t,
                                in_0:W8.t Array2144.t, in_offset:W64.t,
                                bytes:W64.t) : W8.t Array64.t * W64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult bytes)) {
      out.[(W64.to_uint out_offset)] <- in_0.[(W64.to_uint in_offset)];
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
      out_offset <- (out_offset + (W64.of_int 1));
    }
    return (out, out_offset, in_offset);
  }

  proc __memcpy_u8u8_2_32_2144 (out:W8.t Array32.t, out_offset:W64.t,
                                in_0:W8.t Array2144.t, in_offset:W64.t,
                                bytes:W64.t) : W8.t Array32.t * W64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult bytes)) {
      out.[(W64.to_uint out_offset)] <- in_0.[(W64.to_uint in_offset)];
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
      out_offset <- (out_offset + (W64.of_int 1));
    }
    return (out, out_offset, in_offset);
  }

  proc __memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                        in_offset:W64.t, bytes:W64.t) : W64.t * W64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult bytes)) {
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (out_ptr + out_offset)) ((loadW8 Glob.mem (W64.to_uint (in_ptr + in_offset))));
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
      out_offset <- (out_offset + (W64.of_int 1));
    }
    return (out_ptr, out_offset, in_offset);
  }

  proc _memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                       in_offset:W64.t, bytes:W64.t) : W64.t * W64.t * W64.t = {

    (out_ptr, out_offset, in_offset) <@ __memcpy_u8pu8p (out_ptr, out_offset,
    in_ptr, in_offset, bytes);
    return (out_ptr, out_offset, in_offset);
  }

  proc _x__memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                          in_offset:W64.t, bytes:W64.t) : W64.t * W64.t *
                                                          W64.t = {

    out_ptr <- out_ptr;
    out_offset <- out_offset;
    in_ptr <- in_ptr;
    in_offset <- in_offset;
    bytes <- bytes;
    (out_ptr, out_offset, in_offset) <@ _memcpy_u8pu8p (out_ptr, out_offset,
    in_ptr, in_offset, bytes);
    out_ptr <- out_ptr;
    out_offset <- out_offset;
    in_offset <- in_offset;
    return (out_ptr, out_offset, in_offset);
  }

  proc __memcpy_u8pu8_4 (out:W64.t, offset:W64.t, in_0:W8.t Array4.t) : 
  W64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 4))) {
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (out + offset)) (in_0.[(W64.to_uint i)]);
      offset <- (offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc __memcpy_u8pu8_32 (out:W64.t, offset:W64.t, in_0:W8.t Array32.t) : 
  W64.t * W64.t = {

    var i:W64.t;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      Glob.mem <-
      storeW8 Glob.mem (W64.to_uint (out + offset)) (in_0.[(W64.to_uint i)]);
      offset <- (offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return (out, offset);
  }

  proc _memcpy_u8pu8_4 (out:W64.t, offset:W64.t, in_0:W8.t Array4.t) : 
  W64.t * W64.t = {

    (out, offset) <@ __memcpy_u8pu8_4 (out, offset, in_0);
    return (out, offset);
  }

  proc _memcpy_u8pu8_32 (out:W64.t, offset:W64.t, in_0:W8.t Array32.t) : 
  W64.t * W64.t = {

    (out, offset) <@ __memcpy_u8pu8_32 (out, offset, in_0);
    return (out, offset);
  }

  proc _x_memcpy_u8pu8_4 (out:W64.t, offset:W64.t, in_0:W8.t Array4.t) : 
  W64.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8pu8_4 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _x_memcpy_u8pu8_32 (out:W64.t, offset:W64.t, in_0:W8.t Array32.t) : 
  W64.t * W64.t = {

    out <- out;
    offset <- offset;
    in_0 <- in_0;
    (out, offset) <@ _memcpy_u8pu8_32 (out, offset, in_0);
    out <- out;
    offset <- offset;
    return (out, offset);
  }

  proc _zero_address (addr:W32.t Array8.t) : W32.t Array8.t = {
    var aux: int;

    var i:int;

    i <- 0;
    while (i < 8) {
      addr.[i] <- (W32.of_int 0);
      i <- i + 1;
    }
    return (addr);
  }

  proc __zero_address (addr:W32.t Array8.t) : W32.t Array8.t = {

    addr <- addr;
    addr <@ _zero_address (addr);
    addr <- addr;
    return (addr);
  }

  proc __set_layer_addr (addr:W32.t Array8.t, layer:W32.t) : W32.t Array8.t = {

    addr.[0] <- layer;
    return (addr);
  }

  proc __set_tree_addr (addr:W32.t Array8.t, tree:W64.t) : W32.t Array8.t = {

    var t:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    t <- tree;
    (_of_, _cf_, _sf_,  _0, _zf_, t) <- SHR_64 t (W8.of_int 32);
    addr.[1] <- (truncateu32 t);
    addr.[2] <- (truncateu32 tree);
    return (addr);
  }

  proc __set_type (addr:W32.t Array8.t, type_0:W32.t) : W32.t Array8.t = {

    addr.[3] <- type_0;
    return (addr);
  }

  proc __set_key_and_mask (addr:W32.t Array8.t, key_and_mask:W32.t) : 
  W32.t Array8.t = {

    addr.[7] <- key_and_mask;
    return (addr);
  }

  proc __copy_subtree_addr (out:W32.t Array8.t, in_0:W32.t Array8.t) : 
  W32.t Array8.t = {

    out.[0] <- in_0.[0];
    out.[1] <- in_0.[1];
    out.[2] <- in_0.[2];
    return (out);
  }

  proc __set_ots_addr (addr:W32.t Array8.t, ots:W32.t) : W32.t Array8.t = {

    addr.[4] <- ots;
    return (addr);
  }

  proc __set_chain_addr (addr:W32.t Array8.t, chain:W32.t) : W32.t Array8.t = {

    addr.[5] <- chain;
    return (addr);
  }

  proc __set_hash_addr (addr:W32.t Array8.t, hash:W32.t) : W32.t Array8.t = {

    addr.[6] <- hash;
    return (addr);
  }

  proc __set_ltree_addr (addr:W32.t Array8.t, ltree:W32.t) : W32.t Array8.t = {

    addr.[4] <- ltree;
    return (addr);
  }

  proc __set_tree_height (addr:W32.t Array8.t, tree_height:W32.t) : W32.t Array8.t = {

    addr.[5] <- tree_height;
    return (addr);
  }

  proc __set_tree_index (addr:W32.t Array8.t, tree_index:W32.t) : W32.t Array8.t = {

    addr.[6] <- tree_index;
    return (addr);
  }

  proc __addr_to_bytes (addr_as_bytes:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t = {
    var aux: int;

    var i:int;
    var buf:W8.t Array4.t;
    buf <- witness;
    i <- 0;
    while (i < 8) {
      buf <- (Array4.init (fun i_0 => addr_as_bytes.[(4 * i) + i_0]));
      buf <@ __u32_to_bytes (buf, addr.[i]);
      addr_as_bytes <- Array32.init
                       (fun i_0 => if (4 * i) <= i_0 < (4 * i) + 4
                       then buf.[i_0-(4 * i)] else addr_as_bytes.[i_0]);
      i <- i + 1;
    }
    return (addr_as_bytes);
  }

  proc __prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                     key:W8.t Array32.t) : W8.t Array32.t = {

    var buf:W8.t Array128.t;
    var padding_buf:W8.t Array32.t;
    var offset:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    buf <- witness;
    padding_buf <- witness;
    padding_buf <- (Array32.init (fun i => buf.[0 + i]));
    padding_buf <@ __ull_to_bytes_32 (padding_buf, (W64.of_int 4));
    buf <- Array128.init
           (fun i => if 0 <= i < 0 + 32 then padding_buf.[i-0] else buf.[i]);
    offset <- (W64.of_int 32);
    (buf,  _0) <@ _x_memcpy_u8u8_128_32 (buf, offset, key);
    offset <- (W64.of_int (32 + 32));
    (buf,  _1) <@ _x_memcpy_u8u8_128_64 (buf, offset, in_0);
    out <- Hash_128 out buf;
    return (out);
  }

  proc _prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                    key:W8.t Array32.t) : W8.t Array32.t = {

    out <@ __prf_keygen (out, in_0, key);
    return (out);
  }

  proc __prf_keygen_ (out:W8.t Array32.t, in_0:W8.t Array64.t,
                      key:W8.t Array32.t) : W8.t Array32.t = {

    out <- out;
    in_0 <- in_0;
    key <- key;
    out <@ _prf_keygen (out, in_0, key);
    return (out);
  }

  proc __hash_message (mhash:W8.t Array32.t, r:W8.t Array32.t,
                       root:W8.t Array32.t, idx:W64.t,
                       m_with_prefix_ptr:W64.t, mlen:W64.t) : W8.t Array32.t = {

    var buf:W8.t Array32.t;
    var offset:W64.t;
    var buf_n:W8.t Array32.t;
    var len:W64.t;
    buf <- witness;
    buf_n <- witness;
    buf <@ __ull_to_bytes_32 (buf, (W64.of_int 2));
    offset <- (W64.of_int 0);
    (m_with_prefix_ptr, offset) <@ _x_memcpy_u8pu8_32 (m_with_prefix_ptr,
    offset, buf);
    offset <- (W64.of_int 32);
    (m_with_prefix_ptr, offset) <@ _x_memcpy_u8pu8_32 (m_with_prefix_ptr,
    offset, r);
    offset <- (W64.of_int (32 + 32));
    (m_with_prefix_ptr, offset) <@ _x_memcpy_u8pu8_32 (m_with_prefix_ptr,
    offset, root);
    buf_n <@ __ull_to_bytes_32 (buf_n, idx);
    offset <- (W64.of_int (32 + (2 * 32)));
    (m_with_prefix_ptr, offset) <@ _x_memcpy_u8pu8_32 (m_with_prefix_ptr,
    offset, buf_n);
    len <- mlen;
    len <- (len + (W64.of_int (32 + (3 * 32))));
    mhash <- Hash_ptr mhash m_with_prefix_ptr len;
    return (mhash);
  }

  proc _hash_message (mhash:W8.t Array32.t, r:W8.t Array32.t,
                      root:W8.t Array32.t, idx:W64.t,
                      m_with_prefix_ptr:W64.t, mlen:W64.t) : W8.t Array32.t = {

    mhash <@ __hash_message (mhash, r, root, idx, m_with_prefix_ptr, mlen);
    return (mhash);
  }

  proc __hash_message_ (mhash:W8.t Array32.t, r:W8.t Array32.t,
                        root:W8.t Array32.t, idx:W64.t,
                        m_with_prefix_ptr:W64.t, mlen:W64.t) : W8.t Array32.t = {

    mhash <- mhash;
    r <- r;
    root <- root;
    idx <- idx;
    m_with_prefix_ptr <- m_with_prefix_ptr;
    mlen <- mlen;
    mhash <@ _hash_message (mhash, r, root, idx, m_with_prefix_ptr, mlen);
    mhash <- mhash;
    return (mhash);
  }

  proc __thash_h (out:W8.t Array32.t, in_0:W8.t Array64.t,
                  pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                  W32.t Array8.t = {
    var aux: W8.t Array32.t;

    var buf:W8.t Array128.t;
    var addr_as_bytes:W8.t Array32.t;
    var bitmask:W8.t Array64.t;
    var i:W64.t;
    var t:W8.t;
    addr_as_bytes <- witness;
    bitmask <- witness;
    buf <- witness;
    aux <@ __ull_to_bytes_32 ((Array32.init (fun i_0 => buf.[0 + i_0])),
    (W64.of_int 1));
    buf <- Array128.init
           (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0] else buf.[i_0]);
    addr <@ __set_key_and_mask (addr, (W32.of_int 0));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);

    aux <- PRF (Array32.init (fun i_0 => buf.[32 + i_0])) addr_as_bytes pub_seed;
    buf <- Array128.init
           (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
           else buf.[i_0]);

    addr <@ __set_key_and_mask (addr, (W32.of_int 1));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);

    aux <- PRF (Array32.init (fun i_0 => bitmask.[0 + i_0])) addr_as_bytes pub_seed;
    bitmask <- Array64.init
               (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0]
               else bitmask.[i_0]);

    addr <@ __set_key_and_mask (addr, (W32.of_int 2));

    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);

    aux <- PRF (Array32.init (fun i_0 => bitmask.[32 + i_0])) addr_as_bytes pub_seed;
    bitmask <- Array64.init
               (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
               else bitmask.[i_0]);

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int (2 * 32)))) {
      t <- in_0.[(W64.to_uint i)];
      t <- (t `^` bitmask.[(W64.to_uint i)]);
      buf.[(W64.to_uint ((W64.of_int (32 + 32)) + i))] <- t;
      i <- (i + (W64.of_int 1));
    }

    out <- Hash_128 out buf;

    return (out, addr);
  }

  proc _thash_h (out:W8.t Array32.t, in_0:W8.t Array64.t,
                 pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                 W32.t Array8.t = {

    (out, addr) <@ __thash_h (out, in_0, pub_seed, addr);
    return (out, addr);
  }

  proc __thash_h_ (out:W8.t Array32.t, in_0:W8.t Array64.t,
                   pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                   W32.t Array8.t = {

    out <- out;
    in_0 <- in_0;
    pub_seed <- pub_seed;
    addr <- addr;
    (out, addr) <@ _thash_h (out, in_0, pub_seed, addr);
    out <- out;
    addr <- addr;
    return (out, addr);
  }

  proc __thash_f (out:W8.t Array32.t, pub_seed:W8.t Array32.t,
                  addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {
    var aux: W8.t Array32.t;

    var buf:W8.t Array96.t;
    var addr_as_bytes:W8.t Array32.t;
    var bitmask:W8.t Array32.t;
    var i:W64.t;
    var t:W8.t;
    addr_as_bytes <- witness;
    bitmask <- witness;
    buf <- witness;
    aux <@ __ull_to_bytes_32 ((Array32.init (fun i_0 => buf.[0 + i_0])),
    (W64.of_int 0));
    buf <- Array96.init
           (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0] else buf.[i_0]);
    addr <@ __set_key_and_mask (addr, (W32.of_int 0));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);

    aux <- PRF (Array32.init (fun i_0 => buf.[32 + i_0])) addr_as_bytes pub_seed;
    buf <- Array96.init
           (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
           else buf.[i_0]);

    addr <@ __set_key_and_mask (addr, (W32.of_int 1));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);

    bitmask <- PRF bitmask addr_as_bytes pub_seed;

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      t <- out.[(W64.to_uint i)];
      t <- (t `^` bitmask.[(W64.to_uint i)]);
      buf.[(W64.to_uint ((W64.of_int (32 + 32)) + i))] <- t;
      i <- (i + (W64.of_int 1));
    }
    out <- Hash_96 out buf;

    return (out, addr);
  }

  proc _thash_f (out:W8.t Array32.t, pub_seed:W8.t Array32.t,
                 addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {

    (out, addr) <@ __thash_f (out, pub_seed, addr);
    return (out, addr);
  }

  proc __thash_f_ (out:W8.t Array32.t, pub_seed:W8.t Array32.t,
                   addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {

    out <- out;
    pub_seed <- pub_seed;
    addr <- addr;
    (out, addr) <@ _thash_f (out, pub_seed, addr);
    out <- out;
    addr <- addr;
    return (out, addr);
  }

  proc __expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux_1: int;
    var aux_0: W64.t;
    var aux: W8.t Array32.t;

    var offset:W64.t;
    var buf:W8.t Array64.t;
    var i:int;
    var  _0:W64.t;
    buf <- witness;

    addr <@ __set_hash_addr (addr, (W32.of_int 0));
    addr <@ __set_key_and_mask (addr, (W32.of_int 0));
    offset <- (W64.of_int 0);
    (aux,
    aux_0) <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i_0 => buf.[0 + i_0])),
    offset, pub_seed);
    buf <- Array64.init
           (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0] else buf.[i_0]);
     _0 <- aux_0;
    i <- 0;
    while (i < 67) {
      addr <@ __set_chain_addr (addr, (W32.of_int i));

      aux <@ __addr_to_bytes ((Array32.init (fun i_0 => buf.[32 + i_0])),
      addr);
      buf <- Array64.init
             (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
             else buf.[i_0]);

      aux <@ __prf_keygen_ ((Array32.init (fun i_0 => outseeds.[(i * 32) + i_0])),
      buf, inseed);
      outseeds <- Array2144.init
                  (fun i_0 => if (i * 32) <= i_0 < (i * 32) + 32
                  then aux.[i_0-(i * 32)] else outseeds.[i_0]);

      i <- i + 1;
    }

    return (outseeds, addr);
  }

  proc _expand_seed (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                     pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {

    (outseeds, addr) <@ __expand_seed (outseeds, inseed, pub_seed, addr);
    return (outseeds, addr);
  }

  proc __expand_seed_ (outseeds:W8.t Array2144.t, inseed:W8.t Array32.t,
                       pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {

    outseeds <- outseeds;
    inseed <- inseed;
    pub_seed <- pub_seed;
    addr <- addr;
    (outseeds, addr) <@ _expand_seed (outseeds, inseed, pub_seed, addr);
    outseeds <- outseeds;
    addr <- addr;
    return (outseeds, addr);
  }

  proc __gen_chain (out:W8.t Array32.t, in_ptr:W64.t, start:W32.t,
                    steps:W32.t, pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {

    var offset:W64.t;
    var i:W32.t;
    var t:W32.t;
    var cond:bool;
    var  _0:W64.t;

    offset <- (W64.of_int 0);
    (out,  _0) <@ _x_memcpy_u8u8p_32 (out, offset, in_ptr, (W64.of_int 32));

    i <- start;
    t <- start;
    t <- (t + steps);
    cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    while (cond) {

      addr <@ __set_hash_addr (addr, i);

      (out, addr) <@ __thash_f (out, pub_seed, addr);

      i <- (i + (W32.of_int 1));
      cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    }

    return (out, addr);
  }

  proc _gen_chain (out:W8.t Array32.t, in_0:W64.t, start:W32.t, steps:W32.t,
                   pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                   W32.t Array8.t = {

    (out, addr) <@ __gen_chain (out, in_0, start, steps, pub_seed, addr);
    return (out, addr);
  }

  proc __gen_chain_ (out:W8.t Array32.t, in_0:W64.t, start:W32.t,
                     steps:W32.t, pub_seed:W8.t Array32.t,
                     addr:W32.t Array8.t) : W8.t Array32.t * W32.t Array8.t = {

    out <- out;
    in_0 <- in_0;
    start <- start;
    steps <- steps;
    pub_seed <- pub_seed;
    addr <- addr;
    (out, addr) <@ _gen_chain (out, in_0, start, steps, pub_seed, addr);
    out <- out;
    addr <- addr;
    return (out, addr);
  }

  proc __gen_chain_inplace (out:W8.t Array32.t, in_0:W8.t Array32.t,
                            start:W32.t, steps:W32.t,
                            pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {

    var offset:W64.t;
    var i:W32.t;
    var t:W32.t;
    var cond:bool;
    var  _0:W64.t;

    offset <- (W64.of_int 0);
    (out,  _0) <@ _x_memcpy_u8u8_32_32 (out, offset, in_0);

    i <- start;
    t <- start;
    t <- (t + steps);
    cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    while (cond) {

      addr <@ __set_hash_addr (addr, i);

      (out, addr) <@ __thash_f_ (out, pub_seed, addr);

      i <- (i + (W32.of_int 1));
      cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    }

    return (out, addr);
  }

  proc _gen_chain_inplace (out:W8.t Array32.t, in_0:W8.t Array32.t,
                           start:W32.t, steps:W32.t, pub_seed:W8.t Array32.t,
                           addr:W32.t Array8.t) : W8.t Array32.t *
                                                  W32.t Array8.t = {

    (out, addr) <@ __gen_chain_inplace (out, in_0, start, steps, pub_seed,
    addr);
    return (out, addr);
  }

  proc __gen_chain_inplace_ (out:W8.t Array32.t, in_0:W8.t Array32.t,
                             start:W32.t, steps:W32.t,
                             pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {

    out <- out;
    in_0 <- in_0;
    start <- start;
    steps <- steps;
    pub_seed <- pub_seed;
    addr <- addr;
    (out, addr) <@ _gen_chain_inplace (out, in_0, start, steps, pub_seed,
    addr);
    out <- out;
    addr <- addr;
    return (out, addr);
  }

  proc __base_w_3_2 (output:W32.t Array3.t, input:W8.t Array2.t) : W32.t Array3.t = {

    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var consumed:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    in_0 <- (W64.of_int 0);
    out <- (W64.of_int 0);
    bits <- (W64.of_int 0);
    consumed <- (W64.of_int 0);

    while ((consumed \ult (W64.of_int 3))) {
      if ((bits = (W64.of_int 0))) {
        total <- input.[(W64.to_uint in_0)];
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      } 
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      (_of_, _cf_, _sf_,  _0, _zf_, total_32) <- SHR_32 total_32
      (truncateu8 bits);
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output.[(W64.to_uint out)] <- total_32;
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + (W64.of_int 1));
    }
    return (output);
  }

  proc __base_w_67_32 (output:W32.t Array67.t, input:W8.t Array32.t) : 
  W32.t Array67.t = {

    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var consumed:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    in_0 <- (W64.of_int 0);
    out <- (W64.of_int 0);
    bits <- (W64.of_int 0);
    consumed <- (W64.of_int 0);

    while ((consumed \ult (W64.of_int 67))) {
      if ((bits = (W64.of_int 0))) {
        total <- input.[(W64.to_uint in_0)];
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      } 
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      (_of_, _cf_, _sf_,  _0, _zf_, total_32) <- SHR_32 total_32
      (truncateu8 bits);
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output.[(W64.to_uint out)] <- total_32;
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + (W64.of_int 1));
    }
    return (output);
  }

  proc __wots_checksum (csum_base_w:W32.t Array3.t,
                        msg_base_w:W32.t Array67.t) : W32.t Array3.t = {

    var csum:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    var k:int;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var csum_bytes:W8.t Array2.t;
    var csum_bytes_p:W8.t Array2.t;
    var  _0:bool;
    csum_bytes <- witness;
    csum_bytes_p <- witness;
    csum <- (W64.of_int 0);
    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 64))) {
      t <- (W64.of_int (16 - 1));
      u <- (zeroextu64 msg_base_w.[(W64.to_uint i)]);
      t <- (t - u);
      csum <- (csum + t);
      i <- (i + (W64.of_int 1));
    }
    k <- ((3 * 4) %% 8);
    u <- (W64.of_int 8);
    u <- (u - (W64.of_int k));
    (_of_, _cf_, _sf_,  _0, _zf_, csum) <- SHL_64 csum (truncateu8 u);
    csum_bytes_p <- csum_bytes;
    csum_bytes_p <@ __ull_to_bytes_2 (csum_bytes_p, csum);
    csum_base_w <@ __base_w_3_2 (csum_base_w, csum_bytes_p);
    return (csum_base_w);
  }

  proc __chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {

    var t:W32.t Array3.t;
    t <- witness;
    lengths <@ __base_w_67_32 (lengths, msg);
    t <- (Array3.init (fun i => lengths.[64 + i]));
    t <@ __wots_checksum (t, lengths);
    lengths <- Array67.init
               (fun i => if 64 <= i < 64 + 3 then t.[i-64] else lengths.[i]);
    return (lengths);
  }

  proc _chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {

    lengths <@ __chain_lengths (lengths, msg);
    return (lengths);
  }

  proc __chain_lengths_ (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {

    lengths <- lengths;
    msg <- msg;
    lengths <@ _chain_lengths (lengths, msg);
    lengths <- lengths;
    return (lengths);
  }

  proc __wots_pkgen (pk:W8.t Array2144.t, seed:W8.t Array32.t,
                     pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux: int;
    var aux_0: W8.t Array32.t;
    var aux_1: W32.t Array8.t;

    var i:int;
    var chain:W32.t;
    var j:int;
    var buf:W8.t Array32.t;
    buf <- witness;

    (pk, addr) <@ __expand_seed_ (pk, seed, pub_seed, addr);

    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);

      j <- 0;
      while (j < 32) {
        buf.[j] <- pk.[((i * 32) + j)];
        j <- j + 1;
      }
      (aux_0,
      aux_1) <@ __gen_chain_inplace_ ((Array32.init (fun i_0 => pk.[(i * 32) + i_0])),
      buf, (W32.of_int 0), (W32.of_int (16 - 1)), pub_seed, addr);
      pk <- Array2144.init
            (fun i_0 => if (i * 32) <= i_0 < (i * 32) + 32
            then aux_0.[i_0-(i * 32)] else pk.[i_0]);
      addr <- aux_1;

      i <- i + 1;
    }

    return (pk, addr);
  }

  proc __wots_sign (sig:W8.t Array2144.t, msg:W8.t Array32.t,
                    seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                    addr:W32.t Array8.t) : W8.t Array2144.t * W32.t Array8.t = {
    var aux: int;
    var aux_0: W8.t Array32.t;
    var aux_1: W32.t Array8.t;

    var lengths:W32.t Array67.t;
    var i:int;
    var chain:W32.t;
    var j:int;
    var buf:W8.t Array32.t;
    buf <- witness;
    lengths <- witness;

    lengths <@ __chain_lengths_ (lengths, msg);
    (sig, addr) <@ __expand_seed_ (sig, seed, pub_seed, addr);
    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);

      j <- 0;
      while (j < 32) {
        buf.[j] <- sig.[((i * 32) + j)];
        j <- j + 1;
      }
      (aux_0,
      aux_1) <@ __gen_chain_inplace ((Array32.init (fun i_0 => sig.[(i * 32) + i_0])),
      buf, (W32.of_int 0), lengths.[i], pub_seed, addr);
      sig <- Array2144.init
             (fun i_0 => if (i * 32) <= i_0 < (i * 32) + 32
             then aux_0.[i_0-(i * 32)] else sig.[i_0]);
      addr <- aux_1;
      i <- i + 1;
    }
    return (sig, addr);
  }

  proc _wots_sign (sig:W8.t Array2144.t, msg:W8.t Array32.t,
                   seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                   addr:W32.t Array8.t) : W8.t Array2144.t * W32.t Array8.t = {

    (sig, addr) <@ __wots_sign (sig, msg, seed, pub_seed, addr);
    return (sig, addr);
  }

  proc __wots_sign_ (sig:W8.t Array2144.t, msg:W8.t Array32.t,
                     seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                     addr:W32.t Array8.t) : W8.t Array2144.t * W32.t Array8.t = {

    sig <- sig;
    msg <- msg;
    seed <- seed;
    pub_seed <- pub_seed;
    addr <- addr;
    (sig, addr) <@ _wots_sign (sig, msg, seed, pub_seed, addr);
    sig <- sig;
    addr <- addr;
    return (sig, addr);
  }

  proc __wots_pk_from_sig (pk:W8.t Array2144.t, sig_ptr:W64.t,
                           msg:W8.t Array32.t, pub_seed:W8.t Array32.t,
                           addr:W32.t Array8.t) : W8.t Array2144.t *
                                                  W32.t Array8.t = {
    var aux: int;
    var aux_0: W8.t Array32.t;
    var aux_1: W32.t Array8.t;

    var lengths:W32.t Array67.t;
    var i:int;
    var chain:W32.t;
    var start:W32.t;
    var steps:W32.t;
    var t:W64.t;
    lengths <- witness;

    lengths <@ __chain_lengths_ (lengths, msg);
    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);

      start <- lengths.[i];
      steps <- (W32.of_int (16 - 1));
      steps <- (steps - lengths.[i]);
      t <- sig_ptr;
      t <- (t + (W64.of_int (i * 32)));
      (aux_0,
      aux_1) <@ __gen_chain_ ((Array32.init (fun i_0 => pk.[(i * 32) + i_0])),
      t, start, steps, pub_seed, addr);
      pk <- Array2144.init
            (fun i_0 => if (i * 32) <= i_0 < (i * 32) + 32
            then aux_0.[i_0-(i * 32)] else pk.[i_0]);
      addr <- aux_1;
      i <- i + 1;
    }
    return (pk, addr);
  }

  proc __wots_pk_from_sig_ (pk:W8.t Array2144.t, sig_ptr:W64.t,
                            msg:W8.t Array32.t, pub_seed:W8.t Array32.t,
                            addr:W32.t Array8.t) : W8.t Array2144.t *
                                                   W32.t Array8.t = {

    pk <- pk;
    sig_ptr <- sig_ptr;
    msg <- msg;
    pub_seed <- pub_seed;
    addr <- addr;
    (pk, addr) <@ __wots_pk_from_sig (pk, sig_ptr, msg, pub_seed, addr);
    pk <- pk;
    addr <- addr;
    return (pk, addr);
  }

  proc __memcmp (a:W8.t Array32.t, b:W8.t Array32.t) : W64.t = {

    var r:W64.t;
    var are_equal:W64.t;
    var acc:W8.t;
    var i:W64.t;
    var t:W8.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var zf:bool;
    var  _0:bool;
    var  _1:W8.t;

    r <- (W64.of_int (- 1));
    are_equal <- (W64.of_int 0);
    acc <- (W8.of_int 0);
    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int 32))) {
      t <- a.[(W64.to_uint i)];
      t <- (t `^` b.[(W64.to_uint i)]);
      acc <- (acc `|` t);
      i <- (i + (W64.of_int 1));
    }
    (_of_, _cf_, _sf_,  _0, zf,  _1) <- AND_8 acc acc;
    r <- (zf ? are_equal : r);
    return (r);
  }

  proc _memcmp (a:W8.t Array32.t, b:W8.t Array32.t) : W64.t = {

    var r:W64.t;

    r <@ __memcmp (a, b);
    return (r);
  }

  proc __memcmp_ (a:W8.t Array32.t, b:W8.t Array32.t) : W64.t = {

    var r:W64.t;

    a <- a;
    b <- b;
    r <@ _memcmp (a, b);
    r <- r;
    return (r);
  }

  proc __l_tree (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                 pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                 W8.t Array2144.t *
                                                                 W32.t Array8.t = {
    var aux: int;

    var l:W64.t;
    var height:W32.t;
    var parent_nodes:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var i:W64.t;
    var tree_index:W32.t;
    var offset_out:W64.t;
    var offset_in:W64.t;
    var bytes:W64.t;
    var buf0:W8.t Array32.t;
    var buf1:W8.t Array64.t;
    var t:W64.t;
    var j:int;
    var  _0:bool;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:W64.t;
    var  _5:W64.t;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:W64.t;
    buf0 <- witness;
    buf1 <- witness;
    l <- (W64.of_int 67);
    height <- (W32.of_int 0);

    addr <@ __set_tree_height (addr, height);

    while (((W64.of_int 1) \ult l)) {
      parent_nodes <- l;
      (_of_, _cf_, _sf_,  _0, _zf_, parent_nodes) <- SHR_64 parent_nodes
      (W8.of_int 1);

      i <- (W64.of_int 0);

      while ((i \ult parent_nodes)) {

        tree_index <- (truncateu32 i);
        addr <@ __set_tree_index (addr, tree_index);

        offset_out <- (W64.of_int 0);
        offset_in <- (i * (W64.of_int 32));
        bytes <- (W64.of_int 32);
        (buf0,  _1,  _2) <@ __memcpy_u8u8_2_32_2144 (buf0, offset_out,
        wots_pk, offset_in, bytes);
        offset_out <- (W64.of_int 0);
        offset_in <- (i * (W64.of_int 2));
        offset_in <- (offset_in * (W64.of_int 32));
        bytes <- (W64.of_int (2 * 32));
        (buf1,  _3,  _4) <@ __memcpy_u8u8_2_64_2144 (buf1, offset_out,
        wots_pk, offset_in, bytes);

        (buf0, addr) <@ __thash_h (buf0, buf1, pub_seed, addr);

        offset_out <- (i * (W64.of_int 32));
        (wots_pk,  _5) <@ __memcpy_u8u8_2144_32 (wots_pk, offset_out, buf0);

        i <- (i + (W64.of_int 1));
      }

      t <- l;
      t <- (t `&` (W64.of_int 1));
      if ((t <> (W64.of_int 0))) {

        offset_out <- l;
        (_of_, _cf_, _sf_,  _7, _zf_, offset_out) <- SHR_64 offset_out
        (W8.of_int 1);
        offset_out <- (offset_out * (W64.of_int 32));
        offset_in <- l;
        offset_in <- (offset_in - (W64.of_int 1));
        offset_in <- (offset_in * (W64.of_int 32));
        j <- 0;
        while (j < 32) {
          wots_pk.[(W64.to_uint (offset_out + (W64.of_int j)))] <-
          wots_pk.[(W64.to_uint (offset_in + (W64.of_int j)))];
          j <- j + 1;
        }

        (_of_, _cf_, _sf_,  _8, _zf_, l) <- SHR_64 l (W8.of_int 1);
        l <- (l + (W64.of_int 1));
      } else {
        (_of_, _cf_, _sf_,  _6, _zf_, l) <- SHR_64 l (W8.of_int 1);
      }

      height <- (height + (W32.of_int 1));
      addr <@ __set_tree_height (addr, height);

    }

    offset_out <- (W64.of_int 0);
    (leaf,  _9) <@ _x_memcpy_u8u8_32_32 (leaf, offset_out,
    (Array32.init (fun i_0 => wots_pk.[0 + i_0])));
    return (leaf, wots_pk, addr);
  }

  proc _l_tree (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                W8.t Array2144.t *
                                                                W32.t Array8.t = {

    (leaf, wots_pk, addr) <@ __l_tree (leaf, wots_pk, pub_seed, addr);
    return (leaf, wots_pk, addr);
  }

  proc __l_tree_ (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                  pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                  W8.t Array2144.t *
                                                                  W32.t Array8.t = {

    leaf <- leaf;
    addr <- addr;
    wots_pk <- wots_pk;
    pub_seed <- pub_seed;
    (leaf, wots_pk, addr) <@ _l_tree (leaf, wots_pk, pub_seed, addr);
    leaf <- leaf;
    wots_pk <- wots_pk;
    addr <- addr;
    return (leaf, wots_pk, addr);
  }

  proc __compute_root (root:W8.t Array32.t, leaf:W8.t Array32.t,
                       leaf_idx:W32.t, _auth_path_ptr:W64.t,
                       pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    var aux: W8.t Array32.t;
    var aux_0: W32.t Array8.t;

    var auth_path_ptr:W64.t;
    var t32:W32.t;
    var offset_out:W64.t;
    var buffer:W8.t Array64.t;
    var len:W64.t;
    var i:W64.t;
    var tree_height:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var thash_in:W8.t Array64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:bool;
    var  _5:W64.t;
    var  _6:W64.t;
    var  _7:bool;
    buffer <- witness;
    thash_in <- witness;
    auth_path_ptr <- _auth_path_ptr;

    t32 <- leaf_idx;
    t32 <- (t32 `&` (W32.of_int 1));
    if ((t32 <> (W32.of_int 0))) {
      offset_out <- (W64.of_int 32);
      (buffer,  _2) <@ _x_memcpy_u8u8_64_32 (buffer, offset_out, leaf);
      offset_out <- (W64.of_int 0);
      len <- (W64.of_int 32);
      (buffer,  _3) <@ _x_memcpy_u8u8p_64 (buffer, offset_out, auth_path_ptr,
      len);
    } else {
      offset_out <- (W64.of_int 0);
      (buffer,  _0) <@ _x_memcpy_u8u8_64_32 (buffer, offset_out, leaf);
      offset_out <- (W64.of_int 32);
      len <- (W64.of_int 32);
      (buffer,  _1) <@ _x_memcpy_u8u8p_64 (buffer, offset_out, auth_path_ptr,
      len);
    }
    auth_path_ptr <- (auth_path_ptr + (W64.of_int 32));

    i <- (W64.of_int 0);

    while ((i \ult (W64.of_int (10 - 1)))) {

      tree_height <- (truncateu32 i);
      addr <@ __set_tree_height (addr, tree_height);

      (_of_, _cf_, _sf_,  _4, _zf_, leaf_idx) <- SHR_32 leaf_idx
      (W8.of_int 1);
      addr <@ __set_tree_index (addr, leaf_idx);

      t32 <- leaf_idx;
      t32 <- (t32 `&` (W32.of_int 1));
      if ((t32 <> (W32.of_int 0))) {
        thash_in <-
        (Array64.init (fun i_0 => get8
        (WArray64.init64 (fun i_0 => (copy_64 (Array8.init (fun i_0 => get64
                                              (WArray64.init8 (fun i_0 => (buffer).[i_0]))
                                              i_0))).[i_0]))
        i_0));
        (aux,
        aux_0) <@ __thash_h ((Array32.init (fun i_0 => buffer.[32 + i_0])),
        thash_in, pub_seed, addr);
        buffer <- Array64.init
                  (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
                  else buffer.[i_0]);
        addr <- aux_0;
        offset_out <- (W64.of_int 0);
        len <- (W64.of_int 32);
        (buffer,  _6) <@ _x_memcpy_u8u8p_64 (buffer, offset_out,
        auth_path_ptr, len);
      } else {
        thash_in <-
        (Array64.init (fun i_0 => get8
        (WArray64.init64 (fun i_0 => (copy_64 (Array8.init (fun i_0 => get64
                                              (WArray64.init8 (fun i_0 => (buffer).[i_0]))
                                              i_0))).[i_0]))
        i_0));
        (aux,
        aux_0) <@ __thash_h ((Array32.init (fun i_0 => buffer.[0 + i_0])),
        thash_in, pub_seed, addr);
        buffer <- Array64.init
                  (fun i_0 => if 0 <= i_0 < 0 + 32 then aux.[i_0-0]
                  else buffer.[i_0]);
        addr <- aux_0;
        offset_out <- (W64.of_int 32);
        len <- (W64.of_int 32);
        (buffer,  _5) <@ _x_memcpy_u8u8p_64 (buffer, offset_out,
        auth_path_ptr, len);
      }

      auth_path_ptr <- (auth_path_ptr + (W64.of_int 32));

      i <- (i + (W64.of_int 1));
    }

    addr <@ __set_tree_height (addr, (W32.of_int (10 - 1)));
    (_of_, _cf_, _sf_,  _7, _zf_, leaf_idx) <- SHR_32 leaf_idx (W8.of_int 1);
    addr <@ __set_tree_index (addr, leaf_idx);

    (root, addr) <@ __thash_h (root, buffer, pub_seed, addr);
    return (root, addr);
  }

  proc _compute_root (root:W8.t Array32.t, leaf:W8.t Array32.t,
                      leaf_idx:W32.t, auth_path_ptr:W64.t,
                      pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {

    (root, addr) <@ __compute_root (root, leaf, leaf_idx, auth_path_ptr,
    pub_seed, addr);
    return (root, addr);
  }

  proc __compute_root_ (root:W8.t Array32.t, leaf:W8.t Array32.t,
                        leaf_idx:W32.t, auth_path_ptr:W64.t,
                        pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {

    root <- root;
    leaf <- leaf;
    leaf_idx <- leaf_idx;
    auth_path_ptr <- auth_path_ptr;
    pub_seed <- pub_seed;
    addr <- addr;
    (root, addr) <@ _compute_root (root, leaf, leaf_idx, auth_path_ptr,
    pub_seed, addr);
    root <- root;
    addr <- addr;
    return (root, addr);
  }

  proc __gen_leaf_wots (leaf:W8.t Array32.t, sk_seed:W8.t Array32.t,
                        pub_seed:W8.t Array32.t, ltree_addr:W32.t Array8.t,
                        ots_addr:W32.t Array8.t) : W8.t Array32.t *
                                                   W32.t Array8.t *
                                                   W32.t Array8.t = {

    var pk:W8.t Array2144.t;
    var  _0:W8.t Array2144.t;
     _0 <- witness;
    pk <- witness;

    (pk, ots_addr) <@ __wots_pkgen (pk, sk_seed, pub_seed, ots_addr);

    (leaf,  _0, ltree_addr) <@ __l_tree_ (leaf, pk, pub_seed, ltree_addr);

    return (leaf, ltree_addr, ots_addr);
  }

  proc _gen_leaf_wots (leaf:W8.t Array32.t, sk_seed:W8.t Array32.t,
                       pub_seed:W8.t Array32.t, ltree_addr:W32.t Array8.t,
                       ots_addr:W32.t Array8.t) : W8.t Array32.t *
                                                  W32.t Array8.t *
                                                  W32.t Array8.t = {

    (leaf, ltree_addr, ots_addr) <@ __gen_leaf_wots (leaf, sk_seed, pub_seed,
    ltree_addr, ots_addr);
    return (leaf, ltree_addr, ots_addr);
  }

  proc __gen_leaf_wots_ (leaf:W8.t Array32.t, sk_seed:W8.t Array32.t,
                         pub_seed:W8.t Array32.t, ltree_addr:W32.t Array8.t,
                         ots_addr:W32.t Array8.t) : W8.t Array32.t *
                                                    W32.t Array8.t *
                                                    W32.t Array8.t = {

    leaf <- leaf;
    sk_seed <- sk_seed;
    pub_seed <- pub_seed;
    ltree_addr <- ltree_addr;
    ots_addr <- ots_addr;
    (leaf, ltree_addr, ots_addr) <@ _gen_leaf_wots (leaf, sk_seed, pub_seed,
    ltree_addr, ots_addr);
    leaf <- leaf;
    ltree_addr <- ltree_addr;
    ots_addr <- ots_addr;
    return (leaf, ltree_addr, ots_addr);
  }

  proc __xmssmt_core_sign_open (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                                smlen:W64.t, pk:W8.t Array64.t) : W64.t = {

    var res_0:W64.t;
    var sm_offset:W64.t;
    var pub_root:W8.t Array32.t;
    var pub_seed:W8.t Array32.t;
    var idx:W64.t;
    var ots_addr:W32.t Array8.t;
    var ltree_addr:W32.t Array8.t;
    var node_addr:W32.t Array8.t;
    var t64:W64.t;
    var offset_out:W64.t;
    var offset_in:W64.t;
    var bytes:W64.t;
    var buf:W8.t Array32.t;
    var idx_hash:W64.t;
    var root:W8.t Array32.t;
    var i:W32.t;
    var idx_leaf:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var wots_pk:W8.t Array2144.t;
    var leaf:W8.t Array32.t;
    var are_equal:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:bool;
    var  _5:W64.t;
    var  _6:W64.t;
    var  _7:W64.t;
    buf <- witness;
    leaf <- witness;
    ltree_addr <- witness;
    node_addr <- witness;
    ots_addr <- witness;
    pub_root <- witness;
    pub_seed <- witness;
    root <- witness;
    wots_pk <- witness;
    sm_offset <- (W64.of_int 0);
    pub_root <- (Array32.init (fun i_0 => pk.[0 + i_0]));
    pub_seed <- (Array32.init (fun i_0 => pk.[32 + i_0]));
    idx <- (W64.of_int 0);

    ots_addr <@ __zero_address (ots_addr);
    ltree_addr <@ __zero_address (ltree_addr);
    node_addr <@ __zero_address (node_addr);
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    ltree_addr <@ __set_type (ltree_addr, (W32.of_int 1));
    node_addr <@ __set_type (node_addr, (W32.of_int 2));
    t64 <- smlen;
    t64 <- (t64 - (W64.of_int 2500));
    Glob.mem <-
    storeW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))) (t64);
    idx <@ __bytes_to_ull_ptr (sm_ptr, (W64.of_int 4));

    offset_out <- (W64.of_int 2500);
    offset_in <- (W64.of_int 2500);
    bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
    ( _0,  _1,  _2) <@ _x__memcpy_u8pu8p (m_ptr, offset_out, sm_ptr,
    offset_in, bytes);
    offset_out <- (W64.of_int 0);
    t64 <- sm_ptr;
    t64 <- (t64 + (W64.of_int 4));
    bytes <- (W64.of_int 32);
    (buf,  _3) <@ _x_memcpy_u8u8p_32 (buf, offset_out, t64, bytes);
    t64 <- m_ptr;
    t64 <- (t64 + (W64.of_int ((2500 - 32) - (3 * 32))));
    bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
    idx_hash <- idx;
    root <@ __hash_message (root, buf,
    (Array32.init (fun i_0 => pk.[0 + i_0])), idx_hash, t64, bytes);
    t64 <- (W64.of_int (4 + 32));
    sm_offset <- (sm_offset + t64);
    i <- (W32.of_int 0);

    while ((i \ult (W32.of_int 1))) {

      idx_leaf <- (W32.of_int ((1 `<<` 10) - 1));
      idx_leaf <- (idx_leaf `&` (truncateu32 idx));
      (_of_, _cf_, _sf_,  _4, _zf_, idx) <- SHR_64 idx (W8.of_int 10);

      ots_addr <@ __set_layer_addr (ots_addr, i);
      ltree_addr <@ __set_layer_addr (ltree_addr, i);
      node_addr <@ __set_layer_addr (node_addr, i);
      ltree_addr <@ __set_tree_addr (ltree_addr, idx);
      ots_addr <@ __set_tree_addr (ots_addr, idx);
      node_addr <@ __set_tree_addr (node_addr, idx);
      ots_addr <@ __set_ots_addr (ots_addr, idx_leaf);

      t64 <- sm_ptr;
      t64 <- (t64 + sm_offset);
      root <- root;
      (wots_pk, ots_addr) <@ __wots_pk_from_sig_ (wots_pk, t64, root,
      pub_seed, ots_addr);
      t64 <- sm_offset;
      t64 <- (t64 + (W64.of_int 2144));
      sm_offset <- t64;

      ltree_addr <@ __set_ltree_addr (ltree_addr, idx_leaf);

      (leaf, wots_pk, ltree_addr) <@ __l_tree_ (leaf, wots_pk, pub_seed,
      ltree_addr);

      t64 <- sm_ptr;
      t64 <- (t64 + sm_offset);
      idx_leaf <- idx_leaf;
      root <- root;
      (root, node_addr) <@ __compute_root_ (root, leaf, idx_leaf, t64,
      pub_seed, node_addr);
      t64 <- sm_offset;
      t64 <- (t64 + (W64.of_int (10 * 32)));
      sm_offset <- t64;

      i <- (i + (W32.of_int 1));
    }

    are_equal <@ __memcmp_ (root, pub_root);
    if ((are_equal <> (W64.of_int 0))) {
      res_0 <- (W64.of_int (- 1));

      bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
      __memset_u8_ptr (m_ptr, bytes, (W8.of_int 0));
      Glob.mem <-
      storeW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))) ((W64.of_int 0));
    } else {
      res_0 <- (W64.of_int 0);

      bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
      offset_in <- sm_offset;
      ( _5,  _6,  _7) <@ _x__memcpy_u8pu8p (m_ptr, (W64.of_int 0), sm_ptr,
      offset_in, bytes);
    }
    return (res_0);
  }

  proc _xmssmt_core_sign_open (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                               smlen:W64.t, pk:W8.t Array64.t) : W64.t = {

    var res_0:W64.t;

    res_0 <@ __xmssmt_core_sign_open (m_ptr, mlen_ptr, sm_ptr, smlen, pk);
    return (res_0);
  }

  proc __xmssmt_core_sign_open_ (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                                 smlen:W64.t, pk:W8.t Array64.t) : W64.t = {

    var res_0:W64.t;

    m_ptr <- m_ptr;
    mlen_ptr <- mlen_ptr;
    sm_ptr <- sm_ptr;
    smlen <- smlen;
    pk <- pk;
    res_0 <@ _xmssmt_core_sign_open (m_ptr, mlen_ptr, sm_ptr, smlen, pk);
    res_0 <- res_0;
    return (res_0);
  }

  proc __treehash_array (root:W8.t Array32.t, auth_path:W8.t Array320.t,
                         sk_seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                         leaf_idx:W32.t, subtree_addr:W32.t Array8.t) : 
  W8.t Array32.t * W8.t Array320.t = {
    var aux: int;

    var offset:W64.t;
    var ots_addr:W32.t Array8.t;
    var ltree_addr:W32.t Array8.t;
    var node_addr:W32.t Array8.t;
    var idx:W32.t;
    var index:W64.t;
    var j:int;
    var _stack:W8.t Array352.t;
    var buf:W8.t Array32.t;
    var heights:W32.t Array11.t;
    var t:W32.t;
    var u:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var tree_idx:W32.t;
    var buf2:W8.t Array64.t;
    var t64:W64.t;
    var cond:bool;
    var a:W32.t;
    var b:W32.t;
    var  _0:bool;
    var  _1:bool;
    _stack <- witness;
    buf <- witness;
    buf2 <- witness;
    heights <- witness;
    ltree_addr <- witness;
    node_addr <- witness;
    ots_addr <- witness;
    offset <- (W64.of_int 0);

    ots_addr <@ __zero_address (ots_addr);
    ltree_addr <@ __zero_address (ltree_addr);
    node_addr <@ __zero_address (node_addr);
    ots_addr <@ __copy_subtree_addr (ots_addr, subtree_addr);
    ltree_addr <@ __copy_subtree_addr (ltree_addr, subtree_addr);
    node_addr <@ __copy_subtree_addr (node_addr, subtree_addr);
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    ltree_addr <@ __set_type (ltree_addr, (W32.of_int 1));
    node_addr <@ __set_type (node_addr, (W32.of_int 2));
    idx <- (W32.of_int 0);

    while ((idx \ult (W32.of_int (1 `<<` 10)))) {

      ltree_addr <@ __set_ltree_addr (ltree_addr, idx);
      ots_addr <@ __set_ots_addr (ots_addr, idx);

      j <- 0;
      while (j < 32) {
        index <- offset;
        index <- (index * (W64.of_int 32));
        buf.[j] <- _stack.[(W64.to_uint (index + (W64.of_int j)))];
        j <- j + 1;
      }
      (buf, ltree_addr, ots_addr) <@ __gen_leaf_wots_ (buf, sk_seed,
      pub_seed, ltree_addr, ots_addr);

      j <- 0;
      while (j < 32) {
        index <- offset;
        index <- (index * (W64.of_int 32));
        _stack.[(W64.to_uint (index + (W64.of_int j)))] <- buf.[j];
        j <- j + 1;
      }
      offset <- (offset + (W64.of_int 1));
      index <- offset;
      index <- (index - (W64.of_int 1));
      heights.[(W64.to_uint index)] <- (W32.of_int 0);

      t <- leaf_idx;
      t <- (t `^` (W32.of_int 1));
      if ((t = idx)) {

        j <- 0;
        while (j < 32) {
          index <- offset;
          index <- (index - (W64.of_int 1));
          index <- (index * (W64.of_int 32));
          auth_path.[j] <- _stack.[(W64.to_uint (index + (W64.of_int j)))];
          j <- j + 1;
        }

      } 

      a <- heights.[(W64.to_uint (offset - (W64.of_int 1)))];
      b <- heights.[(W64.to_uint (offset - (W64.of_int 2)))];
      cond <@ __cond_u64_geq_u64_u32_eq_u32 (offset, (W64.of_int 2), a, b);
      while (cond) {
        index <- offset;
        index <- (index - (W64.of_int 1));
        t <- heights.[(W64.to_uint index)];
        t <- (t + (W32.of_int 1));
        u <- idx;
        (_of_, _cf_, _sf_,  _0, _zf_, u) <- SHR_32 u (truncateu8 t);
        tree_idx <- u;

        node_addr <@ __set_tree_height (node_addr,
        heights.[(W64.to_uint (offset - (W64.of_int 1)))]);
        node_addr <@ __set_tree_index (node_addr, tree_idx);
        index <- offset;
        index <- (index - (W64.of_int 2));
        index <- (index * (W64.of_int 32));
        aux <- (2 * 32);
        j <- 0;
        while (j < aux) {
          buf2.[j] <- _stack.[(W64.to_uint (index + (W64.of_int j)))];
          j <- j + 1;
        }

        (buf, node_addr) <@ __thash_h_ (buf, buf2, pub_seed, node_addr);

        index <- offset;
        index <- (index - (W64.of_int 2));
        index <- (index * (W64.of_int 32));
        j <- 0;
        while (j < 32) {
          _stack.[(W64.to_uint (index + (W64.of_int j)))] <- buf.[j];
          j <- j + 1;
        }
        offset <- (offset - (W64.of_int 1));

        index <- offset;
        index <- (index - (W64.of_int 1));
        t <- heights.[(W64.to_uint index)];
        t <- (t + (W32.of_int 1));
        heights.[(W64.to_uint index)] <- t;

        index <- offset;
        index <- (index - (W64.of_int 1));
        t <- heights.[(W64.to_uint index)];
        u <- leaf_idx;
        (_of_, _cf_, _sf_,  _1, _zf_, u) <- SHR_32 u (truncateu8 t);
        u <- (u `^` (W32.of_int 1));
        if ((u = tree_idx)) {

          index <- offset;
          index <- (index - (W64.of_int 1));
          t64 <- (zeroextu64 heights.[(W64.to_uint index)]);
          t64 <- (t64 * (W64.of_int 32));
          index <- (index * (W64.of_int 32));
          j <- 0;
          while (j < 32) {
            auth_path.[(W64.to_uint (t64 + (W64.of_int j)))] <-
            _stack.[(W64.to_uint (index + (W64.of_int j)))];
            j <- j + 1;
          }

        } 
        a <- heights.[(W64.to_uint (offset - (W64.of_int 1)))];
        b <- heights.[(W64.to_uint (offset - (W64.of_int 2)))];
        cond <@ __cond_u64_geq_u64_u32_eq_u32 (offset, (W64.of_int 2), a, b);
      }

      idx <- (idx + (W32.of_int 1));
    }

    j <- 0;
    while (j < 32) {
      root.[j] <- _stack.[j];
      j <- j + 1;
    }
    return (root, auth_path);
  }

  proc _treehash_array (root:W8.t Array32.t, auth_path:W8.t Array320.t,
                        sk_seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                        leaf_idx:W32.t, subtree_addr:W32.t Array8.t) : 
  W8.t Array32.t * W8.t Array320.t = {

    (root, auth_path) <@ __treehash_array (root, auth_path, sk_seed,
    pub_seed, leaf_idx, subtree_addr);
    return (root, auth_path);
  }

  proc __treehash_array_ (root:W8.t Array32.t, auth_path:W8.t Array320.t,
                          sk_seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                          leaf_idx:W32.t, subtree_addr:W32.t Array8.t) : 
  W8.t Array32.t * W8.t Array320.t = {

    root <- root;
    auth_path <- auth_path;
    sk_seed <- sk_seed;
    pub_seed <- pub_seed;
    leaf_idx <- leaf_idx;
    subtree_addr <- subtree_addr;
    (root, auth_path) <@ _treehash_array (root, auth_path, sk_seed, pub_seed,
    leaf_idx, subtree_addr);
    root <- root;
    auth_path <- auth_path;
    return (root, auth_path);
  }

  proc __xmssmt_core_seed_keypair (pk:W8.t Array64.t, sk:W8.t Array132.t,
                                   seed:W8.t Array96.t) : W8.t Array64.t *
                                                          W8.t Array132.t = {
    var aux_3: int;
    var aux_1: W64.t;
    var aux: W8.t Array4.t;
    var aux_2: W8.t Array32.t;
    var aux_0: W8.t Array64.t;

    var top_tree_addr:W32.t Array8.t;
    var buf:W8.t Array32.t;
    var auth_path:W8.t Array320.t;
    var i:int;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W8.t Array320.t;
     _3 <- witness;
    auth_path <- witness;
    buf <- witness;
    top_tree_addr <- witness;
    top_tree_addr <@ __zero_address (top_tree_addr);
    top_tree_addr <@ __set_layer_addr (top_tree_addr, (W32.of_int (1 - 1)));
    aux <@ __memset_zero_u8_4 ((Array4.init (fun i_0 => sk.[0 + i_0])));
    sk <- Array132.init
          (fun i_0 => if 0 <= i_0 < 0 + 4 then aux.[i_0-0] else sk.[i_0]);
    (aux_0,
    aux_1) <@ _x_memcpy_u8u8_64_64 ((Array64.init (fun i_0 => sk.[4 + i_0])),
    (W64.of_int 0), (Array64.init (fun i_0 => seed.[0 + i_0])));
    sk <- Array132.init
          (fun i_0 => if 4 <= i_0 < 4 + 64 then aux_0.[i_0-4] else sk.[i_0]);
     _0 <- aux_1;
    (aux_2,
    aux_1) <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i_0 => sk.[(4 + (3 * 32)) + i_0])),
    (W64.of_int 0), (Array32.init (fun i_0 => seed.[(2 * 32) + i_0])));
    sk <- Array132.init
          (fun i_0 => if (4 + (3 * 32)) <= i_0 < (4 + (3 * 32)) + 32
          then aux_2.[i_0-(4 + (3 * 32))] else sk.[i_0]);
     _1 <- aux_1;
    (aux_2,
    aux_1) <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i_0 => pk.[32 + i_0])),
    (W64.of_int 0), (Array32.init (fun i_0 => sk.[(4 + (3 * 32)) + i_0])));
    pk <- Array64.init
          (fun i_0 => if 32 <= i_0 < 32 + 32 then aux_2.[i_0-32]
          else pk.[i_0]);
     _2 <- aux_1;

    (buf,  _3) <@ __treehash_array_ (buf, auth_path,
    (Array32.init (fun i_0 => sk.[4 + i_0])),
    (Array32.init (fun i_0 => pk.[32 + i_0])), (W32.of_int 0),
    top_tree_addr);

    i <- 0;
    while (i < 32) {
      pk.[i] <- buf.[i];
      i <- i + 1;
    }
    i <- 0;
    while (i < 32) {
      sk.[((4 + (2 * 32)) + i)] <- pk.[i];
      i <- i + 1;
    }
    return (pk, sk);
  }

  proc __xmssmt_core_keypair (pk:W8.t Array64.t, sk:W8.t Array132.t) : 
  W8.t Array64.t * W8.t Array132.t = {

    var seed:W8.t Array96.t;
    var seed_p:W8.t Array96.t;
    seed <- witness;
    seed_p <- witness;
    seed_p <- seed;
    seed_p <@ SC.randombytes_96 (seed_p);
    (pk, sk) <@ __xmssmt_core_seed_keypair (pk, sk, seed);
    return (pk, sk);
  }

  proc _xmssmt_core_keypair (pk:W8.t Array64.t, sk:W8.t Array132.t) : 
  W8.t Array64.t * W8.t Array132.t = {

    (pk, sk) <@ __xmssmt_core_keypair (pk, sk);
    return (pk, sk);
  }

  proc __xmssmt_core_keypair_ (pk:W8.t Array64.t, sk:W8.t Array132.t) : 
  W8.t Array64.t * W8.t Array132.t = {

    pk <- pk;
    sk <- sk;
    (pk, sk) <@ _xmssmt_core_keypair (pk, sk);
    pk <- pk;
    sk <- sk;
    return (pk, sk);
  }

  proc __xmssmt_core_sign (sk:W8.t Array132.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                           m_ptr:W64.t, mlen:W64.t) : W8.t Array132.t * W64.t = {
    var aux_1: int;
    var aux: W8.t Array4.t;
    var aux_2: W8.t Array32.t;
    var aux_0: W8.t Array128.t;

    var res_0:W64.t;
    var ots_addr:W32.t Array8.t;
    var t64:W64.t;
    var idx:W64.t;
    var exit_0:W8.t;
    var idx_bytes:W8.t Array32.t;
    var sk_prf:W8.t Array32.t;
    var buf:W8.t Array32.t;
    var pub_root:W8.t Array32.t;
    var j:int;
    var idx_hash:W64.t;
    var root:W8.t Array32.t;
    var i:W32.t;
    var idx_leaf:W32.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var sk_seed:W8.t Array32.t;
    var pub_seed:W8.t Array32.t;
    var sig:W8.t Array2144.t;
    var auth_path:W8.t Array320.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:W64.t;
    var  _5:bool;
    auth_path <- witness;
    buf <- witness;
    idx_bytes <- witness;
    ots_addr <- witness;
    pub_root <- witness;
    pub_seed <- witness;
    root <- witness;
    sig <- witness;
    sk_prf <- witness;
    sk_seed <- witness;

    ots_addr <@ __zero_address (ots_addr);
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    ( _0,  _1,  _2) <@ _x__memcpy_u8pu8p (sm_ptr, (W64.of_int 2500), m_ptr,
    (W64.of_int 0), mlen);
    t64 <- mlen;
    t64 <- (t64 + (W64.of_int 2500));
    Glob.mem <-
    storeW64 Glob.mem (W64.to_uint (smlen_ptr + (W64.of_int 0))) (t64);
    idx <@ __bytes_to_ull_4 ((Array4.init (fun i_0 => sk.[0 + i_0])));

    if (((W64.of_int ((1 `<<` 10) - 1)) \ule idx)) {

      aux <@ __memset_u8_4 ((Array4.init (fun i_0 => sk.[0 + i_0])),
      (W8.of_int 255));
      sk <- Array132.init
            (fun i_0 => if 0 <= i_0 < 0 + 4 then aux.[i_0-0] else sk.[i_0]);
      aux_0 <@ __memset_u8_128 ((Array128.init (fun i_0 => sk.[4 + i_0])),
      (W8.of_int 0));
      sk <- Array132.init
            (fun i_0 => if 4 <= i_0 < 4 + 128 then aux_0.[i_0-4]
            else sk.[i_0]);

      if (((W64.of_int ((1 `<<` 10) - 1)) \ult idx)) {
        exit_0 <- (W8.of_int 1);
      } 
      if (((idx = (W64.of_int ((1 `<<` 10) - 1))) /\ (10 = 64))) {
        exit_0 <- (W8.of_int 1);
      } 
    } 
    if ((exit_0 <> (W8.of_int 1))) {
      (sm_ptr,  _3) <@ _x_memcpy_u8pu8_4 (sm_ptr, (W64.of_int 0),
      (Array4.init (fun i_0 => sk.[0 + i_0])));

      t64 <- idx;
      t64 <- (t64 + (W64.of_int 1));
      aux <@ __ull_to_bytes_4 ((Array4.init (fun i_0 => sk.[0 + i_0])), t64);
      sk <- Array132.init
            (fun i_0 => if 0 <= i_0 < 0 + 4 then aux.[i_0-0] else sk.[i_0]);

      idx_bytes <@ __ull_to_bytes_32 (idx_bytes, idx);
      sk_prf <- (Array32.init (fun i_0 => sk.[(4 + 32) + i_0]));
      buf <- PRF buf idx_bytes sk_prf;
      (sm_ptr,  _4) <@ _x_memcpy_u8pu8_32 (sm_ptr, (W64.of_int 4), buf);

      pub_root <- (Array32.init (fun i_0 => sk.[(4 + (2 * 32)) + i_0]));
      j <- 0;
      while (j < 32) {
        buf.[j] <-
        (loadW8 Glob.mem (W64.to_uint (sm_ptr + (W64.of_int (4 + j)))));
        j <- j + 1;
      }
      idx_hash <- idx;
      t64 <- sm_ptr;
      t64 <- (t64 + (W64.of_int ((2500 - 32) - (3 * 32))));
      aux_2 <@ __hash_message_ ((Array32.init (fun i_0 => root.[0 + i_0])),
      buf, pub_root, idx_hash, t64, mlen);
      root <- Array32.init
              (fun i_0 => if 0 <= i_0 < 0 + 32 then aux_2.[i_0-0]
              else root.[i_0]);
      sm_ptr <- (sm_ptr + (W64.of_int (4 + 32)));

      ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
      i <- (W32.of_int 0);

      while ((i \ult (W32.of_int 1))) {

        idx_leaf <- (W32.of_int ((1 `<<` 10) - 1));
        idx_leaf <- (idx_leaf `&` (truncateu32 idx));
        (_of_, _cf_, _sf_,  _5, _zf_, idx) <- SHR_64 idx (W8.of_int 10);

        ots_addr <@ __set_layer_addr (ots_addr, i);
        ots_addr <@ __set_tree_addr (ots_addr, idx);
        ots_addr <@ __set_ots_addr (ots_addr, idx_leaf);

        sk_seed <- (Array32.init (fun i_0 => sk.[4 + i_0]));
        pub_seed <- (Array32.init (fun i_0 => sk.[(4 + (3 * 32)) + i_0]));
        root <- root;
        (sig, ots_addr) <@ __wots_sign_ (sig, root, sk_seed, pub_seed,
        ots_addr);

        aux_1 <- (67 * 32);
        j <- 0;
        while (j < aux_1) {
          Glob.mem <-
          storeW8 Glob.mem (W64.to_uint (sm_ptr + (W64.of_int j))) (sig.[j]);
          j <- j + 1;
        }
        sm_ptr <- (sm_ptr + (W64.of_int 2144));

        sk_seed <- (Array32.init (fun i_0 => sk.[4 + i_0]));
        pub_seed <- (Array32.init (fun i_0 => sk.[(4 + (3 * 32)) + i_0]));
        aux_1 <- (10 * 32);
        j <- 0;
        while (j < aux_1) {
          auth_path.[j] <-
          (loadW8 Glob.mem (W64.to_uint (sm_ptr + (W64.of_int j))));
          j <- j + 1;
        }
        (root, auth_path) <@ __treehash_array_ (root, auth_path, sk_seed,
        pub_seed, idx_leaf, ots_addr);

        aux_1 <- (10 * 32);
        j <- 0;
        while (j < aux_1) {
          Glob.mem <-
          storeW8 Glob.mem (W64.to_uint (sm_ptr + (W64.of_int j))) (auth_path.[j]);
          j <- j + 1;
        }

        sm_ptr <- (sm_ptr + (W64.of_int (10 * 32)));

        i <- (i + (W32.of_int 1));
      }
    } 
    if ((exit_0 = (W8.of_int 1))) {
      res_0 <- (W64.of_int (- 2));
    } else {
      res_0 <- (W64.of_int 0);
    }
    return (sk, res_0);
  }

  proc __xmss_keypair (pk:W8.t Array68.t, sk:W8.t Array136.t) : W8.t Array68.t *
                                                                W8.t Array136.t = {
    var aux: W8.t Array64.t;
    var aux_0: W8.t Array132.t;

    var oid:W32.t;

    oid <- (W32.of_int 1);
    oid <- BSWAP_32 oid;
    pk <-
    Array68.init
    (WArray68.get8 (WArray68.set32 (WArray68.init8 (fun i => (pk).[i])) 0 (oid)));
    sk <-
    Array136.init
    (WArray136.get8 (WArray136.set32 (WArray136.init8 (fun i => (sk).[i])) 0 (oid)));
    (aux,
    aux_0) <@ __xmssmt_core_keypair_ ((Array64.init (fun i => pk.[4 + i])),
    (Array132.init (fun i => sk.[4 + i])));
    pk <- Array68.init
          (fun i => if 4 <= i < 4 + 64 then aux.[i-4] else pk.[i]);
    sk <- Array136.init
          (fun i => if 4 <= i < 4 + 132 then aux_0.[i-4] else sk.[i]);
    return (pk, sk);
  }

  proc __xmss_sign (sk:W8.t Array136.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                    m_ptr:W64.t, mlen:W64.t) : W8.t Array136.t * W64.t = {
    var aux_0: W64.t;
    var aux: W8.t Array132.t;

    var res_0:W64.t;

    (aux,
    aux_0) <@ __xmssmt_core_sign ((Array132.init (fun i => sk.[4 + i])),
    sm_ptr, smlen_ptr, m_ptr, mlen);
    sk <- Array136.init
          (fun i => if 4 <= i < 4 + 132 then aux.[i-4] else sk.[i]);
    res_0 <- aux_0;
    return (sk, res_0);
  }

  proc __xmss_sign_open (pk:W8.t Array68.t, m_ptr:W64.t, mlen_ptr:W64.t,
                         sm_ptr:W64.t, smlen:W64.t) : W64.t = {

    var res_0:W64.t;

    res_0 <@ __xmssmt_core_sign_open_ (m_ptr, mlen_ptr, sm_ptr, smlen,
    (Array64.init (fun i => pk.[4 + i])));
    return (res_0);
  }

  proc xmss_keypair_jazz (pk:W8.t Array68.t, sk:W8.t Array136.t) : W8.t Array68.t *
                                                                   W8.t Array136.t *
                                                                   W64.t = {

    var res_0:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;

    (pk, sk) <@ __xmss_keypair (pk, sk);
    (_of_, _cf_, _sf_,  _0, _zf_, res_0) <- set0_64 ;
    return (pk, sk, res_0);
  }

  proc xmss_sign_jazz (sk:W8.t Array136.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                       m_ptr:W64.t, mlen:W64.t) : W8.t Array136.t * W64.t = {

    var res_0:W64.t;

    (sk, res_0) <@ __xmss_sign (sk, sm_ptr, smlen_ptr, m_ptr, mlen);
    return (sk, res_0);
  }

  proc xmss_sign_open_jazz (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                            smlen:W64.t, pk:W8.t Array68.t) : W64.t = {

    var res_0:W64.t;

    res_0 <@ __xmss_sign_open (pk, m_ptr, mlen_ptr, sm_ptr, smlen);
    return (res_0);
  }
}.

