require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array2 Array3 Array4 Array8 Array11 Array32 Array64 Array67 Array68 Array96
Array128 Array131 Array135 Array320 Array352 Array2144 Array2464 Array4963.

require import
WArray2 WArray3 WArray4 WArray12 WArray32 WArray44 WArray64 WArray68 WArray96
WArray128 WArray131 WArray135 WArray256 WArray268 WArray320 WArray352
WArray2144 WArray2464 WArray4963.

abbrev sHA256_K =
(Array64.of_list witness
[(W32.of_int 1116352408); (W32.of_int 1899447441);
(W32.of_int (-1245643825)); (W32.of_int (-373957723));
(W32.of_int 961987163); (W32.of_int 1508970993); (W32.of_int (-1841331548));
(W32.of_int (-1424204075)); (W32.of_int (-670586216));
(W32.of_int 310598401); (W32.of_int 607225278); (W32.of_int 1426881987);
(W32.of_int 1925078388); (W32.of_int (-2132889090));
(W32.of_int (-1680079193)); (W32.of_int (-1046744716));
(W32.of_int (-459576895)); (W32.of_int (-272742522)); (W32.of_int 264347078);
(W32.of_int 604807628); (W32.of_int 770255983); (W32.of_int 1249150122);
(W32.of_int 1555081692); (W32.of_int 1996064986); (W32.of_int (-1740746414));
(W32.of_int (-1473132947)); (W32.of_int (-1341970488));
(W32.of_int (-1084653625)); (W32.of_int (-958395405));
(W32.of_int (-710438585)); (W32.of_int 113926993); (W32.of_int 338241895);
(W32.of_int 666307205); (W32.of_int 773529912); (W32.of_int 1294757372);
(W32.of_int 1396182291); (W32.of_int 1695183700); (W32.of_int 1986661051);
(W32.of_int (-2117940946)); (W32.of_int (-1838011259));
(W32.of_int (-1564481375)); (W32.of_int (-1474664885));
(W32.of_int (-1035236496)); (W32.of_int (-949202525));
(W32.of_int (-778901479)); (W32.of_int (-694614492));
(W32.of_int (-200395387)); (W32.of_int 275423344); (W32.of_int 430227734);
(W32.of_int 506948616); (W32.of_int 659060556); (W32.of_int 883997877);
(W32.of_int 958139571); (W32.of_int 1322822218); (W32.of_int 1537002063);
(W32.of_int 1747873779); (W32.of_int 1955562222); (W32.of_int 2024104815);
(W32.of_int (-2067236844)); (W32.of_int (-1933114872));
(W32.of_int (-1866530822)); (W32.of_int (-1538233109));
(W32.of_int (-1090935817)); (W32.of_int (-965641998))]).

module type Syscall_t = {
  proc randombytes_96 (_:W8.t Array96.t) : W8.t Array96.t
}.

module Syscall : Syscall_t = {
  proc randombytes_96 (a:W8.t Array96.t) : W8.t Array96.t = {
    
    a <$
    (dmap WArray96.darray
    (fun a => (Array96.init (fun i => (WArray96.get8 a i)))));
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc __initH_ref () : W32.t Array8.t = {
    var h:W32.t Array8.t;
    h <- witness;
    h.[0] <- (W32.of_int 1779033703);
    h.[1] <- (W32.of_int 3144134277);
    h.[2] <- (W32.of_int 1013904242);
    h.[3] <- (W32.of_int 2773480762);
    h.[4] <- (W32.of_int 1359893119);
    h.[5] <- (W32.of_int 2600822924);
    h.[6] <- (W32.of_int 528734635);
    h.[7] <- (W32.of_int 1541459225);
    return h;
  }
  proc __load_H_ref (h:W32.t Array8.t) : W32.t * W32.t * W32.t * W32.t *
                                         W32.t * W32.t * W32.t * W32.t *
                                         W32.t Array8.t = {
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    var e:W32.t;
    var f:W32.t;
    var g:W32.t;
    var h_0:W32.t;
    a <- h.[0];
    b <- h.[1];
    c <- h.[2];
    d <- h.[3];
    e <- h.[4];
    f <- h.[5];
    g <- h.[6];
    h_0 <- h.[7];
    return (a, b, c, d, e, f, g, h_0, h);
  }
  proc __store_H_ref (h:W32.t Array8.t, a:W32.t, b:W32.t, c:W32.t, d:W32.t,
                      e:W32.t, f:W32.t, g:W32.t, h_0:W32.t) : W32.t Array8.t = {
    
    h.[0] <- a;
    h.[1] <- b;
    h.[2] <- c;
    h.[3] <- d;
    h.[4] <- e;
    h.[5] <- f;
    h.[6] <- g;
    h.[7] <- h_0;
    return h;
  }
  proc __SHR_ref (x:W32.t, c:int) : W32.t = {
    var r:W32.t;
    r <- x;
    r <- (r `>>` (W8.of_int c));
    return r;
  }
  proc __ROTR_ref (x:W32.t, c:int) : W32.t = {
    var r:W32.t;
    var  _0:bool;
    var  _1:bool;
    r <- x;
    ( _0,  _1, r) <- (ROR_32 r (W8.of_int c));
    return r;
  }
  proc __CH_ref (x:W32.t, y:W32.t, z:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <- x;
    r <- (r `&` y);
    s <- x;
    s <- (invw s);
    s <- (s `&` z);
    r <- (r `^` s);
    return r;
  }
  proc __MAJ_ref (x:W32.t, y:W32.t, z:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <- x;
    r <- (r `&` y);
    s <- x;
    s <- (s `&` z);
    r <- (r `^` s);
    s <- y;
    s <- (s `&` z);
    r <- (r `^` s);
    return r;
  }
  proc __BSIG0_ref (x:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <@ __ROTR_ref (x, 2);
    s <@ __ROTR_ref (x, 13);
    r <- (r `^` s);
    s <@ __ROTR_ref (x, 22);
    r <- (r `^` s);
    return r;
  }
  proc __BSIG1_ref (x:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <@ __ROTR_ref (x, 6);
    s <@ __ROTR_ref (x, 11);
    r <- (r `^` s);
    s <@ __ROTR_ref (x, 25);
    r <- (r `^` s);
    return r;
  }
  proc __SSIG0_ref (x:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <@ __ROTR_ref (x, 7);
    s <@ __ROTR_ref (x, 18);
    r <- (r `^` s);
    s <@ __SHR_ref (x, 3);
    r <- (r `^` s);
    return r;
  }
  proc __SSIG1_ref (x:W32.t) : W32.t = {
    var r:W32.t;
    var s:W32.t;
    r <@ __ROTR_ref (x, 17);
    s <@ __ROTR_ref (x, 19);
    r <- (r `^` s);
    s <@ __SHR_ref (x, 10);
    r <- (r `^` s);
    return r;
  }
  proc __Wt_ref (w:W32.t Array64.t, t:int) : W32.t Array64.t = {
    var wt2:W32.t;
    var wt:W32.t;
    var wt15:W32.t;
    wt2 <- w.[(t - 2)];
    wt <@ __SSIG1_ref (wt2);
    wt <- (wt + w.[(t - 7)]);
    wt15 <- w.[(t - 15)];
    wt15 <@ __SSIG0_ref (wt15);
    wt <- (wt + wt15);
    wt <- (wt + w.[(t - 16)]);
    w.[t] <- wt;
    return w;
  }
  proc _blocks_1_ref (_H:W32.t Array8.t, sblocks:W32.t Array32.t,
                      nblocks:W64.t) : W32.t Array8.t * W32.t Array32.t = {
    var aux:int;
    var kp:W32.t Array64.t;
    var hp:W32.t Array8.t;
    var i:W64.t;
    var h:W32.t Array8.t;
    var oblocks:W64.t;
    var t:int;
    var v:W32.t;
    var w:W32.t Array64.t;
    var s_sblocks:W32.t Array32.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    var e:W32.t;
    var f:W32.t;
    var g:W32.t;
    var h_0:W32.t;
    var tr:W64.t;
    var t1:W32.t;
    var r:W32.t;
    var t2:W32.t;
    h <- witness;
    hp <- witness;
    kp <- witness;
    w <- witness;
    s_sblocks <- witness;
    kp <- sHA256_K;
    hp <- _H;
    i <- (W64.of_int 0);
    h <- hp;
    while ((i \ult nblocks)) {
      (* Erased call to spill *)
      oblocks <- (i `<<` (W8.of_int 4));
      t <- 0;
      while ((t < 16)) {
        v <- sblocks.[(W64.to_uint (oblocks + (W64.of_int t)))];
        v <- (BSWAP_32 v);
        w.[t] <- v;
        t <- (t + 1);
      }
      s_sblocks <- sblocks;
      t <- 16;
      while ((t < 64)) {
        w <@ __Wt_ref (w, t);
        t <- (t + 1);
      }
      (a, b, c, d, e, f, g, h_0, h) <@ __load_H_ref (h);
      hp <- h;
      tr <- (W64.of_int 0);
      while ((tr \ult (W64.of_int 64))) {
        t1 <- h_0;
        r <@ __BSIG1_ref (e);
        t1 <- (t1 + r);
        r <@ __CH_ref (e, f, g);
        t1 <- (t1 + r);
        t1 <- (t1 + kp.[(W64.to_uint tr)]);
        t1 <- (t1 + w.[(W64.to_uint tr)]);
        t2 <@ __BSIG0_ref (a);
        r <@ __MAJ_ref (a, b, c);
        t2 <- (t2 + r);
        h_0 <- g;
        g <- f;
        f <- e;
        e <- d;
        e <- (e + t1);
        d <- c;
        c <- b;
        b <- a;
        a <- t1;
        a <- (a + t2);
        tr <- (tr + (W64.of_int 1));
      }
      h <- hp;
      a <- (a + h.[0]);
      b <- (b + h.[1]);
      c <- (c + h.[2]);
      d <- (d + h.[3]);
      e <- (e + h.[4]);
      f <- (f + h.[5]);
      g <- (g + h.[6]);
      h_0 <- (h_0 + h.[7]);
      h <@ __store_H_ref (h, a, b, c, d, e, f, g, h_0);
      sblocks <- s_sblocks;
      (* Erased call to unspill *)
      i <- (i + (W64.of_int 1));
    }
    _H <- h;
    return (_H, sblocks);
  }
  proc __store_ref_array (out:W8.t Array32.t, h:W32.t Array8.t) : W8.t Array32.t = {
    var aux:int;
    var i:int;
    var v:W32.t;
    i <- 0;
    while ((i < 8)) {
      v <- h.[i];
      v <- (BSWAP_32 v);
      out <-
      (Array32.init
      (WArray32.get8
      (WArray32.set32 (WArray32.init8 (fun i_0 => out.[i_0])) i v)));
      i <- (i + 1);
    }
    return out;
  }
  proc _blocks_0_ref_128 (_H:W32.t Array8.t, in_0:W8.t Array128.t) : 
  W32.t Array8.t * W64.t = {
    var aux:int;
    var offset:W64.t;
    var inlen:W64.t;
    var kp:W32.t Array64.t;
    var hp:W32.t Array8.t;
    var h:W32.t Array8.t;
    var t:int;
    var v:W32.t;
    var w:W32.t Array64.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    var e:W32.t;
    var f:W32.t;
    var g:W32.t;
    var h_0:W32.t;
    var tr:W64.t;
    var t1:W32.t;
    var r:W32.t;
    var t2:W32.t;
    h <- witness;
    hp <- witness;
    kp <- witness;
    w <- witness;
    offset <- (W64.of_int 0);
    inlen <- (W64.of_int 128);
    kp <- sHA256_K;
    hp <- _H;
    h <- hp;
    if ((64 <= 128)) {
      while (((W64.of_int 64) \ule inlen)) {
        (* Erased call to spill *)
        t <- 0;
        while ((t < 16)) {
          v <-
          (get32_direct (WArray128.init8 (fun i => in_0.[i]))
          (W64.to_uint (offset + (W64.of_int (4 * t)))));
          v <- (BSWAP_32 v);
          w.[t] <- v;
          t <- (t + 1);
        }
        (* Erased call to spill *)
        t <- 16;
        while ((t < 64)) {
          w <@ __Wt_ref (w, t);
          t <- (t + 1);
        }
        (a, b, c, d, e, f, g, h_0, h) <@ __load_H_ref (h);
        hp <- h;
        tr <- (W64.of_int 0);
        while ((tr \ult (W64.of_int 64))) {
          t1 <- h_0;
          r <@ __BSIG1_ref (e);
          t1 <- (t1 + r);
          r <@ __CH_ref (e, f, g);
          t1 <- (t1 + r);
          t1 <- (t1 + kp.[(W64.to_uint tr)]);
          t1 <- (t1 + w.[(W64.to_uint tr)]);
          t2 <@ __BSIG0_ref (a);
          r <@ __MAJ_ref (a, b, c);
          t2 <- (t2 + r);
          h_0 <- g;
          g <- f;
          f <- e;
          e <- d;
          e <- (e + t1);
          d <- c;
          c <- b;
          b <- a;
          a <- t1;
          a <- (a + t2);
          tr <- (tr + (W64.of_int 1));
        }
        h <- hp;
        a <- (a + h.[0]);
        b <- (b + h.[1]);
        c <- (c + h.[2]);
        d <- (d + h.[3]);
        e <- (e + h.[4]);
        f <- (f + h.[5]);
        g <- (g + h.[6]);
        h_0 <- (h_0 + h.[7]);
        h <@ __store_H_ref (h, a, b, c, d, e, f, g, h_0);
        (* Erased call to unspill *)
        offset <- (offset + (W64.of_int 64));
        inlen <- (inlen - (W64.of_int 64));
      }
    } else {
      
    }
    _H <- h;
    return (_H, offset);
  }
  proc _blocks_0_ref_96 (_H:W32.t Array8.t, in_0:W8.t Array96.t) : W32.t Array8.t *
                                                                   W64.t = {
    var aux:int;
    var offset:W64.t;
    var inlen:W64.t;
    var kp:W32.t Array64.t;
    var hp:W32.t Array8.t;
    var h:W32.t Array8.t;
    var t:int;
    var v:W32.t;
    var w:W32.t Array64.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    var e:W32.t;
    var f:W32.t;
    var g:W32.t;
    var h_0:W32.t;
    var tr:W64.t;
    var t1:W32.t;
    var r:W32.t;
    var t2:W32.t;
    h <- witness;
    hp <- witness;
    kp <- witness;
    w <- witness;
    offset <- (W64.of_int 0);
    inlen <- (W64.of_int 96);
    kp <- sHA256_K;
    hp <- _H;
    h <- hp;
    if ((64 <= 96)) {
      while (((W64.of_int 64) \ule inlen)) {
        (* Erased call to spill *)
        t <- 0;
        while ((t < 16)) {
          v <-
          (get32_direct (WArray96.init8 (fun i => in_0.[i]))
          (W64.to_uint (offset + (W64.of_int (4 * t)))));
          v <- (BSWAP_32 v);
          w.[t] <- v;
          t <- (t + 1);
        }
        (* Erased call to spill *)
        t <- 16;
        while ((t < 64)) {
          w <@ __Wt_ref (w, t);
          t <- (t + 1);
        }
        (a, b, c, d, e, f, g, h_0, h) <@ __load_H_ref (h);
        hp <- h;
        tr <- (W64.of_int 0);
        while ((tr \ult (W64.of_int 64))) {
          t1 <- h_0;
          r <@ __BSIG1_ref (e);
          t1 <- (t1 + r);
          r <@ __CH_ref (e, f, g);
          t1 <- (t1 + r);
          t1 <- (t1 + kp.[(W64.to_uint tr)]);
          t1 <- (t1 + w.[(W64.to_uint tr)]);
          t2 <@ __BSIG0_ref (a);
          r <@ __MAJ_ref (a, b, c);
          t2 <- (t2 + r);
          h_0 <- g;
          g <- f;
          f <- e;
          e <- d;
          e <- (e + t1);
          d <- c;
          c <- b;
          b <- a;
          a <- t1;
          a <- (a + t2);
          tr <- (tr + (W64.of_int 1));
        }
        h <- hp;
        a <- (a + h.[0]);
        b <- (b + h.[1]);
        c <- (c + h.[2]);
        d <- (d + h.[3]);
        e <- (e + h.[4]);
        f <- (f + h.[5]);
        g <- (g + h.[6]);
        h_0 <- (h_0 + h.[7]);
        h <@ __store_H_ref (h, a, b, c, d, e, f, g, h_0);
        (* Erased call to unspill *)
        offset <- (offset + (W64.of_int 64));
        inlen <- (inlen - (W64.of_int 64));
      }
    } else {
      
    }
    _H <- h;
    return (_H, offset);
  }
  proc __lastblocks_ref_128 (in_0:W8.t Array128.t, inlen:W64.t, offset:W64.t,
                             bits:W64.t) : W32.t Array32.t * W64.t = {
    var aux:int;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var i:W64.t;
    var k:int;
    var index:W64.t;
    var v:W8.t;
    var j:W64.t;
    sblocks <- witness;
    i <- (W64.of_int 0);
    k <- 0;
    while ((k < 32)) {
      sblocks.[k] <- (truncateu32 i);
      k <- (k + 1);
    }
    while ((i \ult inlen)) {
      index <- offset;
      index <- (index + i);
      v <- in_0.[(W64.to_uint index)];
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) v)));
      i <- (i + (W64.of_int 1));
    }
    sblocks <-
    (Array32.init
    (WArray128.get32
    (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
    (W64.to_uint i) (W8.of_int 128))));
    if ((inlen \ult (W64.of_int 56))) {
      j <- (W64.of_int (64 - 8));
      nblocks <- (W64.of_int 1);
      i <- (W64.of_int 63);
    } else {
      j <- (W64.of_int (128 - 8));
      nblocks <- (W64.of_int 2);
      i <- (W64.of_int 127);
    }
    while ((j \ule i)) {
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) (truncateu8 bits))));
      bits <- (bits `>>` (W8.of_int 8));
      i <- (i - (W64.of_int 1));
    }
    return (sblocks, nblocks);
  }
  proc __lastblocks_ref_96 (in_0:W8.t Array96.t, inlen:W64.t, offset:W64.t,
                            bits:W64.t) : W32.t Array32.t * W64.t = {
    var aux:int;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var i:W64.t;
    var k:int;
    var index:W64.t;
    var v:W8.t;
    var j:W64.t;
    sblocks <- witness;
    i <- (W64.of_int 0);
    k <- 0;
    while ((k < 32)) {
      sblocks.[k] <- (truncateu32 i);
      k <- (k + 1);
    }
    while ((i \ult inlen)) {
      index <- offset;
      index <- (index + i);
      v <- in_0.[(W64.to_uint index)];
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) v)));
      i <- (i + (W64.of_int 1));
    }
    sblocks <-
    (Array32.init
    (WArray128.get32
    (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
    (W64.to_uint i) (W8.of_int 128))));
    if ((inlen \ult (W64.of_int 56))) {
      j <- (W64.of_int (64 - 8));
      nblocks <- (W64.of_int 1);
      i <- (W64.of_int 63);
    } else {
      j <- (W64.of_int (128 - 8));
      nblocks <- (W64.of_int 2);
      i <- (W64.of_int 127);
    }
    while ((j \ule i)) {
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) (truncateu8 bits))));
      bits <- (bits `>>` (W8.of_int 8));
      i <- (i - (W64.of_int 1));
    }
    return (sblocks, nblocks);
  }
  proc __sha256_128 (out:W8.t Array32.t, in_0:W8.t Array128.t) : W8.t Array32.t = {
    var bits:W64.t;
    var h:W32.t Array8.t;
    var hp:W32.t Array8.t;
    var offset:W64.t;
    var inlen:W64.t;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var sblocksp:W32.t Array32.t;
    var  _0:W32.t Array32.t;
     _0 <- witness;
    h <- witness;
    hp <- witness;
    sblocks <- witness;
    sblocksp <- witness;
    (* Erased call to spill *)
    bits <- (W64.of_int 128);
    bits <- (bits `<<` (W8.of_int 3));
    (* Erased call to spill *)
    h <@ __initH_ref ();
    (* Erased call to spill *)
    hp <- h;
    (hp, offset) <@ _blocks_0_ref_128 (hp, in_0);
    (* Erased call to unspill *)
    inlen <- (W64.of_int (128 %% 64));
    (sblocks, nblocks) <@ __lastblocks_ref_128 (in_0, inlen, offset, bits);
    sblocksp <- sblocks;
    (hp,  _0) <@ _blocks_1_ref (hp, sblocksp, nblocks);
    (* Erased call to unspill *)
    h <- hp;
    out <@ __store_ref_array (out, h);
    return out;
  }
  proc __sha256_96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    var bits:W64.t;
    var h:W32.t Array8.t;
    var hp:W32.t Array8.t;
    var offset:W64.t;
    var inlen:W64.t;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var sblocksp:W32.t Array32.t;
    var  _0:W32.t Array32.t;
     _0 <- witness;
    h <- witness;
    hp <- witness;
    sblocks <- witness;
    sblocksp <- witness;
    (* Erased call to spill *)
    bits <- (W64.of_int 96);
    bits <- (bits `<<` (W8.of_int 3));
    (* Erased call to spill *)
    h <@ __initH_ref ();
    (* Erased call to spill *)
    hp <- h;
    (hp, offset) <@ _blocks_0_ref_96 (hp, in_0);
    (* Erased call to unspill *)
    inlen <- (W64.of_int (96 %% 64));
    (sblocks, nblocks) <@ __lastblocks_ref_96 (in_0, inlen, offset, bits);
    sblocksp <- sblocks;
    (hp,  _0) <@ _blocks_1_ref (hp, sblocksp, nblocks);
    (* Erased call to unspill *)
    h <- hp;
    out <@ __store_ref_array (out, h);
    return out;
  }
  proc __store_ref (out:W64.t, h:W32.t Array8.t) : unit = {
    var aux:int;
    var i:int;
    var v:W32.t;
    i <- 0;
    while ((i < 8)) {
      v <- h.[i];
      v <- (BSWAP_32 v);
      Glob.mem <-
      (storeW32 Glob.mem (W64.to_uint (out + (W64.of_int (i * 4)))) v);
      i <- (i + 1);
    }
    return ();
  }
  proc _blocks_0_ref (_H:W32.t Array8.t, in_0:W64.t, inlen:W64.t) : W32.t Array8.t *
                                                                    W64.t *
                                                                    W64.t = {
    var aux:int;
    var kp:W32.t Array64.t;
    var hp:W32.t Array8.t;
    var h:W32.t Array8.t;
    var t:int;
    var v:W32.t;
    var w:W32.t Array64.t;
    var a:W32.t;
    var b:W32.t;
    var c:W32.t;
    var d:W32.t;
    var e:W32.t;
    var f:W32.t;
    var g:W32.t;
    var h_0:W32.t;
    var tr:W64.t;
    var t1:W32.t;
    var r:W32.t;
    var t2:W32.t;
    h <- witness;
    hp <- witness;
    kp <- witness;
    w <- witness;
    kp <- sHA256_K;
    hp <- _H;
    h <- hp;
    while (((W64.of_int 64) \ule inlen)) {
      t <- 0;
      while ((t < 16)) {
        v <- (loadW32 Glob.mem (W64.to_uint (in_0 + (W64.of_int (t * 4)))));
        v <- (BSWAP_32 v);
        w.[t] <- v;
        t <- (t + 1);
      }
      (* Erased call to spill *)
      t <- 16;
      while ((t < 64)) {
        w <@ __Wt_ref (w, t);
        t <- (t + 1);
      }
      (a, b, c, d, e, f, g, h_0, h) <@ __load_H_ref (h);
      hp <- h;
      tr <- (W64.of_int 0);
      while ((tr \ult (W64.of_int 64))) {
        t1 <- h_0;
        r <@ __BSIG1_ref (e);
        t1 <- (t1 + r);
        r <@ __CH_ref (e, f, g);
        t1 <- (t1 + r);
        t1 <- (t1 + kp.[(W64.to_uint tr)]);
        t1 <- (t1 + w.[(W64.to_uint tr)]);
        t2 <@ __BSIG0_ref (a);
        r <@ __MAJ_ref (a, b, c);
        t2 <- (t2 + r);
        h_0 <- g;
        g <- f;
        f <- e;
        e <- d;
        e <- (e + t1);
        d <- c;
        c <- b;
        b <- a;
        a <- t1;
        a <- (a + t2);
        tr <- (tr + (W64.of_int 1));
      }
      h <- hp;
      a <- (a + h.[0]);
      b <- (b + h.[1]);
      c <- (c + h.[2]);
      d <- (d + h.[3]);
      e <- (e + h.[4]);
      f <- (f + h.[5]);
      g <- (g + h.[6]);
      h_0 <- (h_0 + h.[7]);
      h <@ __store_H_ref (h, a, b, c, d, e, f, g, h_0);
      (* Erased call to unspill *)
      in_0 <- (in_0 + (W64.of_int 64));
      inlen <- (inlen - (W64.of_int 64));
    }
    _H <- h;
    return (_H, in_0, inlen);
  }
  proc __lastblocks_ref (in_0:W64.t, inlen:W64.t, bits:W64.t) : W32.t Array32.t *
                                                                W64.t = {
    var aux:int;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var i:W64.t;
    var k:int;
    var v:W8.t;
    var j:W64.t;
    sblocks <- witness;
    i <- (W64.of_int 0);
    k <- 0;
    while ((k < 32)) {
      sblocks.[k] <- (truncateu32 i);
      k <- (k + 1);
    }
    while ((i \ult inlen)) {
      v <- (loadW8 Glob.mem (W64.to_uint (in_0 + i)));
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) v)));
      i <- (i + (W64.of_int 1));
    }
    sblocks <-
    (Array32.init
    (WArray128.get32
    (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
    (W64.to_uint i) (W8.of_int 128))));
    if ((inlen \ult (W64.of_int 56))) {
      j <- (W64.of_int (64 - 8));
      nblocks <- (W64.of_int 1);
      i <- (W64.of_int 63);
    } else {
      j <- (W64.of_int (128 - 8));
      nblocks <- (W64.of_int 2);
      i <- (W64.of_int 127);
    }
    while ((j \ule i)) {
      sblocks <-
      (Array32.init
      (WArray128.get32
      (WArray128.set8 (WArray128.init32 (fun i_0 => sblocks.[i_0]))
      (W64.to_uint i) (truncateu8 bits))));
      bits <- (bits `>>` (W8.of_int 8));
      i <- (i - (W64.of_int 1));
    }
    return (sblocks, nblocks);
  }
  proc __sha256_in_ptr (out:W8.t Array32.t, in_0:W64.t, inlen:W64.t) : 
  W8.t Array32.t = {
    var bits:W64.t;
    var h:W32.t Array8.t;
    var hp:W32.t Array8.t;
    var sblocks:W32.t Array32.t;
    var nblocks:W64.t;
    var sblocksp:W32.t Array32.t;
    var  _0:W32.t Array32.t;
     _0 <- witness;
    h <- witness;
    hp <- witness;
    sblocks <- witness;
    sblocksp <- witness;
    (* Erased call to spill *)
    bits <- inlen;
    bits <- (bits `<<` (W8.of_int 3));
    (* Erased call to spill *)
    h <@ __initH_ref ();
    hp <- h;
    (hp, in_0, inlen) <@ _blocks_0_ref (hp, in_0, inlen);
    (* Erased call to unspill *)
    (sblocks, nblocks) <@ __lastblocks_ref (in_0, inlen, bits);
    sblocksp <- sblocks;
    (hp,  _0) <@ _blocks_1_ref (hp, sblocksp, nblocks);
    (* Erased call to unspill *)
    h <- hp;
    out <@ __store_ref_array (out, h);
    return out;
  }
  proc __core_hash_128 (out:W8.t Array32.t, in_0:W8.t Array128.t) : W8.t Array32.t = {
    
    out <@ __sha256_128 (out, in_0);
    return out;
  }
  proc __core_hash_96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    out <@ __sha256_96 (out, in_0);
    return out;
  }
  proc _core_hash_96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    out <@ __core_hash_96 (out, in_0);
    return out;
  }
  proc _core_hash_128 (out:W8.t Array32.t, in_0:W8.t Array128.t) : W8.t Array32.t = {
    
    out <@ __core_hash_128 (out, in_0);
    return out;
  }
  proc __core_hash__128 (out:W8.t Array32.t, in_0:W8.t Array128.t) : 
  W8.t Array32.t = {
    
    in_0 <- in_0;
    out <- out;
    out <@ _core_hash_128 (out, in_0);
    out <- out;
    return out;
  }
  proc __core_hash__96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    in_0 <- in_0;
    out <- out;
    out <@ _core_hash_96 (out, in_0);
    out <- out;
    return out;
  }
  proc __core_hash_in_ptr (out:W8.t Array32.t, in_ptr:W64.t, inlen:W64.t) : 
  W8.t Array32.t = {
    
    out <@ __sha256_in_ptr (out, in_ptr, inlen);
    return out;
  }
  proc _core_hash_in_ptr (out:W8.t Array32.t, in_ptr:W64.t, inlen:W64.t) : 
  W8.t Array32.t = {
    
    out <@ __core_hash_in_ptr (out, in_ptr, inlen);
    return out;
  }
  proc __core_hash_in_ptr_ (out:W8.t Array32.t, in_ptr:W64.t, inlen:W64.t) : 
  W8.t Array32.t = {
    
    out <- out;
    in_ptr <- in_ptr;
    inlen <- inlen;
    out <@ _core_hash_in_ptr (out, in_ptr, inlen);
    return out;
  }
  proc __u32_to_bytes (out:W8.t Array4.t, in_0:W32.t) : W8.t Array4.t = {
    
    in_0 <- (BSWAP_32 in_0);
    out <-
    (Array4.init
    (WArray4.get8
    (WArray4.set32_direct (WArray4.init8 (fun i => out.[i])) 0 in_0)));
    return out;
  }
  proc __ull_to_bytes_2 (out:W8.t Array2.t, in_0:W64.t) : W8.t Array2.t = {
    var aux:int;
    var i:int;
    in_0 <- in_0;
    aux <- (- 1);
    i <- (2 - 1);
    while ((aux < i)) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- (i - 1);
    }
    return out;
  }
  proc __ull_to_bytes_32 (out:W8.t Array32.t, in_0:W64.t) : W8.t Array32.t = {
    var aux:int;
    var i:int;
    in_0 <- in_0;
    aux <- (- 1);
    i <- (32 - 1);
    while ((aux < i)) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- (i - 1);
    }
    return out;
  }
  proc __ull_to_bytes_3 (out:W8.t Array3.t, in_0:W64.t) : W8.t Array3.t = {
    var aux:int;
    var i:int;
    in_0 <- in_0;
    aux <- (- 1);
    i <- (3 - 1);
    while ((aux < i)) {
      out.[i] <- (truncateu8 in_0);
      in_0 <- (in_0 `>>` (W8.of_int 8));
      i <- (i - 1);
    }
    return out;
  }
  proc __bytes_to_ull (in_0:W8.t Array3.t) : W64.t = {
    var result:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    result <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 3))) {
      t <- (zeroextu64 in_0.[(W64.to_uint i)]);
      u <- (W64.of_int (3 - 1));
      u <- (u - i);
      u <- (u `<<` (W8.of_int 3));
      t <- (t `<<` (truncateu8 (u `&` (W64.of_int 63))));
      result <- (result `|` t);
      i <- (i + (W64.of_int 1));
    }
    return result;
  }
  proc __bytes_to_ull_ptr (in_ptr:W64.t) : W64.t = {
    var result:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    result <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 3))) {
      t <- (zeroextu64 (loadW8 Glob.mem (W64.to_uint (in_ptr + i))));
      u <- (W64.of_int (3 - 1));
      u <- (u - i);
      u <- (u `<<` (W8.of_int 3));
      t <- (t `<<` (truncateu8 (u `&` (W64.of_int 63))));
      result <- (result `|` t);
      i <- (i + (W64.of_int 1));
    }
    return result;
  }
  proc __memset_zero_u8 (a:W8.t Array3.t) : W8.t Array3.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 3))) {
      a.[(W64.to_uint i)] <- (W8.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    return a;
  }
  proc __memset_u8_128 (a:W8.t Array128.t, value:W8.t) : W8.t Array128.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 128))) {
      a.[(W64.to_uint i)] <- value;
      i <- (i + (W64.of_int 1));
    }
    return a;
  }
  proc __memset_u8_3 (a:W8.t Array3.t, value:W8.t) : W8.t Array3.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 3))) {
      a.[(W64.to_uint i)] <- value;
      i <- (i + (W64.of_int 1));
    }
    return a;
  }
  proc __memset_u8_ptr (_ptr:W64.t, inlen:W64.t, value:W8.t) : unit = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult inlen)) {
      Glob.mem <- (storeW8 Glob.mem (W64.to_uint (_ptr + i)) value);
      i <- (i + (W64.of_int 1));
    }
    return ();
  }
  proc __nbytes_copy_offset_131_32 (out:W8.t Array131.t, offset_out:W64.t,
                                    in_0:W8.t Array32.t, offset_in:W64.t) : 
  W8.t Array131.t = {
    var aux:int;
    var i:int;
    i <- 0;
    while ((i < 32)) {
      out.[(W64.to_uint (offset_out + (W64.of_int i)))] <-
      in_0.[(W64.to_uint (offset_in + (W64.of_int i)))];
      i <- (i + 1);
    }
    return out;
  }
  proc __nbytes_copy_offset_64_32 (out:W8.t Array64.t, offset_out:W64.t,
                                   in_0:W8.t Array32.t, offset_in:W64.t) : 
  W8.t Array64.t = {
    var aux:int;
    var i:int;
    i <- 0;
    while ((i < 32)) {
      out.[(W64.to_uint (offset_out + (W64.of_int i)))] <-
      in_0.[(W64.to_uint (offset_in + (W64.of_int i)))];
      i <- (i + 1);
    }
    return out;
  }
  proc __nbytes_copy_inplace_2144 (out:W8.t Array2144.t, offset_out:W64.t,
                                   offset_in:W64.t) : W8.t Array2144.t = {
    var aux:int;
    var i:int;
    i <- 0;
    while ((i < 32)) {
      out.[(W64.to_uint (offset_out + (W64.of_int i)))] <-
      out.[(W64.to_uint (offset_in + (W64.of_int i)))];
      i <- (i + 1);
    }
    return out;
  }
  proc __memcpy_u8u8_offset (out:W8.t Array2144.t, offset:W64.t,
                             in_0:W8.t Array32.t) : W8.t Array2144.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint offset)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
      offset <- (offset + (W64.of_int 1));
    }
    return out;
  }
  proc __memcpy_u8u8_64_64 (out:W8.t Array64.t, in_0:W8.t Array64.t) : 
  W8.t Array64.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      out.[(W64.to_uint i)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    return out;
  }
  proc __memcpy_u8u8_64_32 (out:W8.t Array64.t, in_0:W8.t Array32.t) : 
  W8.t Array64.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint i)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    return out;
  }
  proc __memcpy_u8u8_32_32 (out:W8.t Array32.t, in_0:W8.t Array32.t) : 
  W8.t Array32.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      out.[(W64.to_uint i)] <- in_0.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    return out;
  }
  proc _memcpy_u8u8_64_64 (out:W8.t Array64.t, in_0:W8.t Array64.t) : 
  W8.t Array64.t = {
    
    out <@ __memcpy_u8u8_64_64 (out, in_0);
    return out;
  }
  proc _memcpy_u8u8_64_32 (out:W8.t Array64.t, in_0:W8.t Array32.t) : 
  W8.t Array64.t = {
    
    out <@ __memcpy_u8u8_64_32 (out, in_0);
    return out;
  }
  proc _memcpy_u8u8_32_32 (out:W8.t Array32.t, in_0:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    out <@ __memcpy_u8u8_32_32 (out, in_0);
    return out;
  }
  proc _x_memcpy_u8u8_64_64 (out:W8.t Array64.t, in_0:W8.t Array64.t) : 
  W8.t Array64.t = {
    
    out <- out;
    in_0 <- in_0;
    out <@ _memcpy_u8u8_64_64 (out, in_0);
    out <- out;
    return out;
  }
  proc _x_memcpy_u8u8_64_32 (out:W8.t Array64.t, in_0:W8.t Array32.t) : 
  W8.t Array64.t = {
    
    out <- out;
    in_0 <- in_0;
    out <@ _memcpy_u8u8_64_32 (out, in_0);
    out <- out;
    return out;
  }
  proc _x_memcpy_u8u8_32_32 (out:W8.t Array32.t, in_0:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    out <- out;
    in_0 <- in_0;
    out <@ _memcpy_u8u8_32_32 (out, in_0);
    out <- out;
    return out;
  }
  proc __memcpy_u8u8p (out:W8.t Array32.t, in_ptr:W64.t) : W8.t Array32.t = {
    var aux:int;
    var i:int;
    i <- 0;
    while ((i < 32)) {
      out.[i] <- (loadW8 Glob.mem (W64.to_uint (in_ptr + (W64.of_int i))));
      i <- (i + 1);
    }
    return out;
  }
  proc _memcpy_u8u8p (out:W8.t Array32.t, in_ptr:W64.t) : W8.t Array32.t = {
    
    out <@ __memcpy_u8u8p (out, in_ptr);
    return out;
  }
  proc _x_memcpy_u8u8p (out:W8.t Array32.t, in_ptr:W64.t) : W8.t Array32.t = {
    
    out <- out;
    in_ptr <- in_ptr;
    out <@ _memcpy_u8u8p (out, in_ptr);
    out <- out;
    return out;
  }
  proc __memcpy_u8u8_2_64_2144 (out:W8.t Array64.t, in_0:W8.t Array2144.t,
                                in_offset:W64.t, bytes:W64.t) : W8.t Array64.t *
                                                                W64.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult bytes)) {
      out.[(W64.to_uint i)] <- in_0.[(W64.to_uint in_offset)];
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
    }
    return (out, in_offset);
  }
  proc __memcpy_u8u8_2_64_352 (out:W8.t Array64.t, in_0:W8.t Array352.t,
                               in_offset:W64.t, bytes:W64.t) : W8.t Array64.t *
                                                               W64.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult bytes)) {
      out.[(W64.to_uint i)] <- in_0.[(W64.to_uint in_offset)];
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
    }
    return (out, in_offset);
  }
  proc __memcpy_u8u8_3_352_32 (out:W8.t Array352.t, in_0:W8.t Array32.t,
                               out_offset:W64.t, bytes:int) : W8.t Array352.t = {
    var aux:int;
    var i:int;
    aux <- bytes;
    i <- 0;
    while ((i < aux)) {
      out.[(W64.to_uint (out_offset + (W64.of_int i)))] <- in_0.[i];
      i <- (i + 1);
    }
    return out;
  }
  proc __memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                        in_offset:W64.t, bytes:W64.t) : unit = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult bytes)) {
      Glob.mem <-
      (storeW8 Glob.mem (W64.to_uint (out_ptr + out_offset))
      (loadW8 Glob.mem (W64.to_uint (in_ptr + in_offset))));
      i <- (i + (W64.of_int 1));
      in_offset <- (in_offset + (W64.of_int 1));
      out_offset <- (out_offset + (W64.of_int 1));
    }
    return ();
  }
  proc _memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                       in_offset:W64.t, bytes:W64.t) : unit = {
    
    __memcpy_u8pu8p (out_ptr, out_offset, in_ptr, in_offset, bytes);
    return ();
  }
  proc _x__memcpy_u8pu8p (out_ptr:W64.t, out_offset:W64.t, in_ptr:W64.t,
                          in_offset:W64.t, bytes:W64.t) : unit = {
    
    out_ptr <- out_ptr;
    out_offset <- out_offset;
    in_ptr <- in_ptr;
    in_offset <- in_offset;
    bytes <- bytes;
    _memcpy_u8pu8p (out_ptr, out_offset, in_ptr, in_offset, bytes);
    return ();
  }
  proc __memcpy_u8pu8_32 (out:W64.t, offset:W64.t, in_0:W8.t Array32.t) : 
  W64.t * W64.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      Glob.mem <-
      (storeW8 Glob.mem (W64.to_uint (out + offset)) in_0.[(W64.to_uint i)]);
      offset <- (offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return (out, offset);
  }
  proc _memcpy_u8pu8_32 (out:W64.t, offset:W64.t, in_0:W8.t Array32.t) : 
  W64.t * W64.t = {
    
    (out, offset) <@ __memcpy_u8pu8_32 (out, offset, in_0);
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
    var aux:int;
    var i:int;
    i <- 0;
    while ((i < 8)) {
      addr.[i] <- (W32.of_int 0);
      i <- (i + 1);
    }
    return addr;
  }
  proc __zero_address_ (addr:W32.t Array8.t) : W32.t Array8.t = {
    
    addr <- addr;
    addr <@ _zero_address (addr);
    addr <- addr;
    return addr;
  }
  proc __set_layer_addr (addr:W32.t Array8.t, layer:W32.t) : W32.t Array8.t = {
    
    addr.[0] <- layer;
    return addr;
  }
  proc __set_tree_addr (addr:W32.t Array8.t, tree:W64.t) : W32.t Array8.t = {
    var t:W64.t;
    t <- tree;
    t <- (t `>>` (truncateu8 ((W256.of_int 32) `&` (W256.of_int 63))));
    addr.[1] <- (truncateu32 t);
    addr.[2] <- (truncateu32 tree);
    return addr;
  }
  proc __set_type (addr:W32.t Array8.t, _type:W32.t) : W32.t Array8.t = {
    
    addr.[3] <- _type;
    return addr;
  }
  proc __set_key_and_mask (addr:W32.t Array8.t, key_and_mask:W32.t) : 
  W32.t Array8.t = {
    
    addr.[7] <- key_and_mask;
    return addr;
  }
  proc __copy_subtree_addr (out:W32.t Array8.t, in_0:W32.t Array8.t) : 
  W32.t Array8.t = {
    
    out.[0] <- in_0.[0];
    out.[1] <- in_0.[1];
    out.[2] <- in_0.[2];
    return out;
  }
  proc __set_ots_addr (addr:W32.t Array8.t, ots:W32.t) : W32.t Array8.t = {
    
    addr.[4] <- ots;
    return addr;
  }
  proc __set_chain_addr (addr:W32.t Array8.t, chain:W32.t) : W32.t Array8.t = {
    
    addr.[5] <- chain;
    return addr;
  }
  proc __set_hash_addr (addr:W32.t Array8.t, hash:W32.t) : W32.t Array8.t = {
    
    addr.[6] <- hash;
    return addr;
  }
  proc __set_ltree_addr (addr:W32.t Array8.t, ltree:W32.t) : W32.t Array8.t = {
    
    addr.[4] <- ltree;
    return addr;
  }
  proc __set_tree_height (addr:W32.t Array8.t, tree_height:W32.t) : W32.t Array8.t = {
    
    addr.[5] <- tree_height;
    return addr;
  }
  proc __set_tree_index (addr:W32.t Array8.t, tree_index:W32.t) : W32.t Array8.t = {
    
    addr.[6] <- tree_index;
    return addr;
  }
  proc __addr_to_bytes (addr_as_bytes:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t = {
    var aux:int;
    var i:int;
    var buf:W8.t Array4.t;
    buf <- witness;
    i <- 0;
    while ((i < 8)) {
      buf <- (Array4.init (fun i_0 => addr_as_bytes.[((4 * i) + i_0)]));
      buf <@ __u32_to_bytes (buf, addr.[i]);
      addr_as_bytes <-
      (Array32.init
      (fun i_0 => (if ((4 * i) <= i_0 < ((4 * i) + 4)) then buf.[(i_0 -
                                                                 (4 * i))] else 
                  addr_as_bytes.[i_0]))
      );
      i <- (i + 1);
    }
    return addr_as_bytes;
  }
  proc __prf (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    var aux:W8.t Array32.t;
    var buf:W8.t Array96.t;
    var padding_buf:W8.t Array32.t;
    buf <- witness;
    padding_buf <- witness;
    padding_buf <- (Array32.init (fun i => buf.[(0 + i)]));
    padding_buf <@ __ull_to_bytes_32 (padding_buf, (W64.of_int 3));
    buf <-
    (Array96.init
    (fun i => (if (0 <= i < (0 + 32)) then padding_buf.[(i - 0)] else 
              buf.[i]))
    );
    aux <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i => buf.[(32 + i)])),
    key);
    buf <-
    (Array96.init
    (fun i => (if (32 <= i < (32 + 32)) then aux.[(i - 32)] else buf.[i])));
    aux <@ _x_memcpy_u8u8_32_32 ((Array32.init
                                 (fun i => buf.[((32 + 32) + i)])),
    in_0);
    buf <-
    (Array96.init
    (fun i => (if ((32 + 32) <= i < ((32 + 32) + 32)) then aux.[(i -
                                                                (32 + 32))] else 
              buf.[i]))
    );
    out <@ __core_hash__96 (out, buf);
    return out;
  }
  proc _prf (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    out <@ __prf (out, in_0, key);
    return out;
  }
  proc __prf_ (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    out <- out;
    in_0 <- in_0;
    key <- key;
    out <@ _prf (out, in_0, key);
    out <- out;
    return out;
  }
  proc __prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                     key:W8.t Array32.t) : W8.t Array32.t = {
    var aux:W8.t Array32.t;
    var aux_0:W8.t Array64.t;
    var buf:W8.t Array128.t;
    var padding_buf:W8.t Array32.t;
    buf <- witness;
    padding_buf <- witness;
    padding_buf <- (Array32.init (fun i => buf.[(0 + i)]));
    padding_buf <@ __ull_to_bytes_32 (padding_buf, (W64.of_int 4));
    buf <-
    (Array128.init
    (fun i => (if (0 <= i < (0 + 32)) then padding_buf.[(i - 0)] else 
              buf.[i]))
    );
    aux <@ _x_memcpy_u8u8_32_32 ((Array32.init (fun i => buf.[(32 + i)])),
    key);
    buf <-
    (Array128.init
    (fun i => (if (32 <= i < (32 + 32)) then aux.[(i - 32)] else buf.[i])));
    aux_0 <@ _x_memcpy_u8u8_64_64 ((Array64.init
                                   (fun i => buf.[((32 + 32) + i)])),
    in_0);
    buf <-
    (Array128.init
    (fun i => (if ((32 + 32) <= i < ((32 + 32) + 64)) then aux_0.[(i -
                                                                  (32 + 32))] else 
              buf.[i]))
    );
    out <@ __core_hash__128 (out, buf);
    return out;
  }
  proc _prf_keygen (out:W8.t Array32.t, in_0:W8.t Array64.t,
                    key:W8.t Array32.t) : W8.t Array32.t = {
    
    out <@ __prf_keygen (out, in_0, key);
    return out;
  }
  proc __prf_keygen_ (out:W8.t Array32.t, in_0:W8.t Array64.t,
                      key:W8.t Array32.t) : W8.t Array32.t = {
    
    out <- out;
    in_0 <- in_0;
    key <- key;
    out <@ _prf_keygen (out, in_0, key);
    return out;
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
    mhash <@ __core_hash_in_ptr_ (mhash, m_with_prefix_ptr, len);
    return mhash;
  }
  proc _hash_message (mhash:W8.t Array32.t, r:W8.t Array32.t,
                      root:W8.t Array32.t, idx:W64.t,
                      m_with_prefix_ptr:W64.t, mlen:W64.t) : W8.t Array32.t = {
    
    mhash <@ __hash_message (mhash, r, root, idx, m_with_prefix_ptr, mlen);
    return mhash;
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
    return mhash;
  }
  proc __thash_h (out:W8.t Array32.t, in_0:W8.t Array64.t,
                  pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                  W32.t Array8.t = {
    var aux:W8.t Array32.t;
    var buf:W8.t Array128.t;
    var addr_as_bytes:W8.t Array32.t;
    var bitmask:W8.t Array64.t;
    var i:W64.t;
    var t:W8.t;
    addr_as_bytes <- witness;
    bitmask <- witness;
    buf <- witness;
    aux <@ __ull_to_bytes_32 ((Array32.init (fun i_0 => buf.[(0 + i_0)])),
    (W64.of_int 1));
    buf <-
    (Array128.init
    (fun i_0 => (if (0 <= i_0 < (0 + 32)) then aux.[(i_0 - 0)] else buf.[i_0]))
    );
    addr <@ __set_key_and_mask (addr, (W32.of_int 0));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);
    (* Erased call to spill *)
    aux <@ __prf_ ((Array32.init (fun i_0 => buf.[(32 + i_0)])),
    addr_as_bytes, pub_seed);
    buf <-
    (Array128.init
    (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                buf.[i_0]))
    );
    (* Erased call to unspill *)
    addr <@ __set_key_and_mask (addr, (W32.of_int 1));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);
    (* Erased call to spill *)
    (* Erased call to unspill *)
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[(0 + i_0)])),
    addr_as_bytes, pub_seed);
    bitmask <-
    (Array64.init
    (fun i_0 => (if (0 <= i_0 < (0 + 32)) then aux.[(i_0 - 0)] else bitmask.[
                                                                    i_0]))
    );
    (* Erased call to unspill *)
    addr <@ __set_key_and_mask (addr, (W32.of_int 2));
    (* Erased call to spill *)
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);
    (* Erased call to unspill *)
    aux <@ __prf_ ((Array32.init (fun i_0 => bitmask.[(32 + i_0)])),
    addr_as_bytes, pub_seed);
    bitmask <-
    (Array64.init
    (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                bitmask.[i_0]))
    );
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (2 * 32)))) {
      t <- in_0.[(W64.to_uint i)];
      t <- (t `^` bitmask.[(W64.to_uint i)]);
      buf.[(W64.to_uint ((W64.of_int (32 + 32)) + i))] <- t;
      i <- (i + (W64.of_int 1));
    }
    (* Erased call to unspill *)
    out <@ _core_hash_128 (out, buf);
    (* Erased call to unspill *)
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
    var aux:W8.t Array32.t;
    var addr_as_bytes:W8.t Array32.t;
    var buf:W8.t Array96.t;
    var padding:W8.t Array32.t;
    var bitmask:W8.t Array32.t;
    var i:W64.t;
    var t:W8.t;
    addr_as_bytes <- witness;
    bitmask <- witness;
    buf <- witness;
    padding <- witness;
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);
    padding <- (Array32.init (fun i_0 => buf.[(0 + i_0)]));
    padding <@ __ull_to_bytes_32 (padding, (W64.of_int 0));
    buf <-
    (Array96.init
    (fun i_0 => (if (0 <= i_0 < (0 + 32)) then padding.[(i_0 - 0)] else 
                buf.[i_0]))
    );
    (* Erased call to spill *)
    aux <@ __prf_ ((Array32.init (fun i_0 => buf.[(32 + i_0)])),
    addr_as_bytes, pub_seed);
    buf <-
    (Array96.init
    (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                buf.[i_0]))
    );
    (* Erased call to unspill *)
    addr <@ __set_key_and_mask (addr, (W32.of_int 1));
    addr_as_bytes <@ __addr_to_bytes (addr_as_bytes, addr);
    (* Erased call to spill *)
    (* Erased call to unspill *)
    bitmask <@ __prf_ (bitmask, addr_as_bytes, pub_seed);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      t <- out.[(W64.to_uint i)];
      t <- (t `^` bitmask.[(W64.to_uint i)]);
      buf.[(W64.to_uint ((W64.of_int (32 + 32)) + i))] <- t;
      i <- (i + (W64.of_int 1));
    }
    out <@ __core_hash__96 (out, buf);
    (* Erased call to unspill *)
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
    var aux:int;
    var buf:W8.t Array64.t;
    var i:int;
    var addr_bytes:W8.t Array32.t;
    var ith_seed:W8.t Array32.t;
    addr_bytes <- witness;
    buf <- witness;
    ith_seed <- witness;
    (* Erased call to spill *)
    addr <@ __set_hash_addr (addr, (W32.of_int 0));
    addr <@ __set_key_and_mask (addr, (W32.of_int 0));
    buf <-
    (Array64.init
    (fun i_0 => (if (0 <= i_0 < (0 + 32)) then (copy_8 pub_seed).[(i_0 - 0)] else 
                buf.[i_0]))
    );
    i <- 0;
    while ((i < 67)) {
      addr <@ __set_chain_addr (addr, (W32.of_int i));
      (* Erased call to spill *)
      addr_bytes <- (Array32.init (fun i_0 => buf.[(32 + i_0)]));
      addr_bytes <@ __addr_to_bytes (addr_bytes, addr);
      buf <-
      (Array64.init
      (fun i_0 => (if (32 <= i_0 < (32 + 32)) then addr_bytes.[(i_0 - 32)] else 
                  buf.[i_0]))
      );
      (* Erased call to unspill *)
      ith_seed <- (Array32.init (fun i_0 => outseeds.[((i * 32) + i_0)]));
      ith_seed <@ __prf_keygen_ (ith_seed, buf, inseed);
      outseeds <-
      (Array2144.init
      (fun i_0 => (if ((i * 32) <= i_0 < ((i * 32) + 32)) then ith_seed.[
                                                               (i_0 -
                                                               (i * 32))] else 
                  outseeds.[i_0]))
      );
      (* Erased call to spill *)
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    (* Erased call to unspill *)
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
  proc __gen_chain_inplace (out:W8.t Array32.t, start:W32.t, steps:W32.t,
                            pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    var i:W32.t;
    var t:W32.t;
    (* Erased call to spill *)
    i <- start;
    t <- start;
    t <- (t + steps);
    while ((i \ult t)) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      addr <@ __set_hash_addr (addr, i);
      addr <@ __set_key_and_mask (addr, (W32.of_int 0));
      (* Erased call to unspill *)
      (out, addr) <@ __thash_f_ (out, pub_seed, addr);
      (* Erased call to spill *)
      (* Erased call to unspill *)
      i <- (i + (W32.of_int 1));
    }
    (* Erased call to unspill *)
    return (out, addr);
  }
  proc _gen_chain_inplace (out:W8.t Array32.t, start:W32.t, steps:W32.t,
                           pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    
    (out, addr) <@ __gen_chain_inplace (out, start, steps, pub_seed, addr);
    return (out, addr);
  }
  proc __gen_chain_inplace_ (out:W8.t Array32.t, start:W32.t, steps:W32.t,
                             pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    
    out <- out;
    start <- start;
    steps <- steps;
    pub_seed <- pub_seed;
    addr <- addr;
    (out, addr) <@ _gen_chain_inplace (out, start, steps, pub_seed, addr);
    out <- out;
    addr <- addr;
    return (out, addr);
  }
  proc __base_w_64_32 (output:W32.t Array64.t, input:W8.t Array32.t) : 
  W32.t Array64.t = {
    var aux:int;
    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var consumed:int;
    in_0 <- (W64.of_int 0);
    out <- (W64.of_int 0);
    bits <- (W64.of_int 0);
    total <- (W8.of_int 0);
    consumed <- 0;
    while ((consumed < 64)) {
      if ((bits = (W64.of_int 0))) {
        total <- input.[(W64.to_uint in_0)];
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      } else {
        
      }
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      total_32 <- (total_32 `>>` (truncateu8 (bits `&` (W64.of_int 31))));
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output.[(W64.to_uint out)] <- total_32;
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + 1);
    }
    return output;
  }
  proc __base_w_3_2 (output:W32.t Array3.t, input:W8.t Array2.t) : W32.t Array3.t = {
    var aux:int;
    var in_0:W64.t;
    var out:W64.t;
    var bits:W64.t;
    var total:W8.t;
    var total_32:W32.t;
    var consumed:int;
    in_0 <- (W64.of_int 0);
    out <- (W64.of_int 0);
    bits <- (W64.of_int 0);
    total <- (W8.of_int 0);
    consumed <- 0;
    while ((consumed < 3)) {
      if ((bits = (W64.of_int 0))) {
        total <- input.[(W64.to_uint in_0)];
        in_0 <- (in_0 + (W64.of_int 1));
        bits <- (bits + (W64.of_int 8));
      } else {
        
      }
      bits <- (bits - (W64.of_int 4));
      total_32 <- (zeroextu32 total);
      total_32 <- (total_32 `>>` (truncateu8 (bits `&` (W64.of_int 31))));
      total_32 <- (total_32 `&` (W32.of_int (16 - 1)));
      output.[(W64.to_uint out)] <- total_32;
      out <- (out + (W64.of_int 1));
      consumed <- (consumed + 1);
    }
    return output;
  }
  proc __csum (msg_base_w:W32.t Array64.t) : W64.t = {
    var csum:W64.t;
    var i:W64.t;
    var t:W64.t;
    var u:W64.t;
    csum <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      t <- (W64.of_int (16 - 1));
      u <- (zeroextu64 msg_base_w.[(W64.to_uint i)]);
      t <- (t - u);
      csum <- (csum + t);
      i <- (i + (W64.of_int 1));
    }
    return csum;
  }
  proc __wots_checksum (csum_base_w:W32.t Array3.t,
                        msg_base_w:W32.t Array67.t) : W32.t Array3.t = {
    var buf:W32.t Array64.t;
    var csum:W64.t;
    var k:int;
    var u:W64.t;
    var csum_bytes:W8.t Array2.t;
    var csum_bytes_p:W8.t Array2.t;
    buf <- witness;
    csum_bytes <- witness;
    csum_bytes_p <- witness;
    buf <- (Array64.init (fun i => msg_base_w.[(0 + i)]));
    csum <@ __csum (buf);
    k <- ((3 * 4) %% 8);
    u <- (W64.of_int 8);
    u <- (u - (W64.of_int k));
    csum <- (csum `<<` (truncateu8 (u `&` (W64.of_int 63))));
    csum_bytes_p <- csum_bytes;
    csum_bytes_p <@ __ull_to_bytes_2 (csum_bytes_p, csum);
    csum_base_w <@ __base_w_3_2 (csum_base_w, csum_bytes_p);
    return csum_base_w;
  }
  proc _wots_checksum (csum_base_w:W32.t Array3.t, msg_base_w:W32.t Array67.t) : 
  W32.t Array3.t = {
    
    csum_base_w <@ __wots_checksum (csum_base_w, msg_base_w);
    return csum_base_w;
  }
  proc __wots_checksum_ (csum_base_w:W32.t Array3.t,
                         msg_base_w:W32.t Array67.t) : W32.t Array3.t = {
    
    csum_base_w <- csum_base_w;
    msg_base_w <- msg_base_w;
    csum_base_w <@ _wots_checksum (csum_base_w, msg_base_w);
    csum_base_w <- csum_base_w;
    return csum_base_w;
  }
  proc __chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {
    var t0:W32.t Array64.t;
    var t1:W32.t Array3.t;
    t0 <- witness;
    t1 <- witness;
    t0 <- (Array64.init (fun i => lengths.[(0 + i)]));
    t0 <@ __base_w_64_32 (t0, msg);
    lengths <-
    (Array67.init
    (fun i => (if (0 <= i < (0 + 64)) then t0.[(i - 0)] else lengths.[i])));
    t1 <- (Array3.init (fun i => lengths.[(64 + i)]));
    t1 <@ __wots_checksum (t1, lengths);
    lengths <-
    (Array67.init
    (fun i => (if (64 <= i < (64 + 3)) then t1.[(i - 64)] else lengths.[i])));
    return lengths;
  }
  proc _chain_lengths (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {
    
    lengths <@ __chain_lengths (lengths, msg);
    return lengths;
  }
  proc __chain_lengths_ (lengths:W32.t Array67.t, msg:W8.t Array32.t) : 
  W32.t Array67.t = {
    
    lengths <- lengths;
    msg <- msg;
    lengths <@ _chain_lengths (lengths, msg);
    lengths <- lengths;
    return lengths;
  }
  proc __wots_pkgen (pk:W8.t Array2144.t, seed:W8.t Array32.t,
                     pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array2144.t * W32.t Array8.t = {
    var aux:int;
    var i:int;
    var chain:W32.t;
    var t:W8.t Array32.t;
    t <- witness;
    (* Erased call to spill *)
    (pk, addr) <@ __expand_seed_ (pk, seed, pub_seed, addr);
    (* Erased call to spill *)
    i <- 0;
    while ((i < 67)) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
      t <- (Array32.init (fun i_0 => pk.[((i * 32) + i_0)]));
      (t, addr) <@ __gen_chain_inplace_ (t, (W32.of_int 0),
      (W32.of_int (16 - 1)), pub_seed, addr);
      pk <-
      (Array2144.init
      (fun i_0 => (if ((i * 32) <= i_0 < ((i * 32) + 32)) then t.[(i_0 -
                                                                  (i * 32))] else 
                  pk.[i_0]))
      );
      (* Erased call to spill *)
      i <- (i + 1);
    }
    (* Erased call to unspill *)
    return (pk, addr);
  }
  proc __wots_sign (sig:W8.t Array2144.t, msg:W8.t Array32.t,
                    seed:W8.t Array32.t, pub_seed:W8.t Array32.t,
                    addr:W32.t Array8.t) : W8.t Array2144.t * W32.t Array8.t = {
    var aux:int;
    var aux_0:W8.t Array32.t;
    var aux_1:W32.t Array8.t;
    var lengths:W32.t Array67.t;
    var i:int;
    var chain:W32.t;
    lengths <- witness;
    (* Erased call to spill *)
    lengths <@ __chain_lengths_ (lengths, msg);
    (sig, addr) <@ __expand_seed_ (sig, seed, pub_seed, addr);
    i <- 0;
    while ((i < 67)) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
      (aux_0, aux_1) <@ __gen_chain_inplace_ ((Array32.init
                                              (fun i_0 => sig.[((i * 32) +
                                                               i_0)])
                                              ),
      (W32.of_int 0), lengths.[i], pub_seed, addr);
      sig <-
      (Array2144.init
      (fun i_0 => (if ((i * 32) <= i_0 < ((i * 32) + 32)) then aux_0.[
                                                               (i_0 -
                                                               (i * 32))] else 
                  sig.[i_0]))
      );
      addr <- aux_1;
      i <- (i + 1);
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
    var aux:int;
    var aux_0:W8.t Array32.t;
    var aux_1:W32.t Array8.t;
    var lengths:W32.t Array67.t;
    var i:int;
    var chain:W32.t;
    var start:W32.t;
    var steps:W32.t;
    var t:W64.t;
    lengths <- witness;
    (* Erased call to spill *)
    lengths <@ __chain_lengths_ (lengths, msg);
    i <- 0;
    while ((i < 67)) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
      start <- lengths.[i];
      steps <- (W32.of_int (16 - 1));
      steps <- (steps - lengths.[i]);
      t <- sig_ptr;
      t <- (t + (W64.of_int (i * 32)));
      aux_0 <@ _x_memcpy_u8u8p ((Array32.init
                                (fun i_0 => pk.[((i * 32) + i_0)])),
      t);
      pk <-
      (Array2144.init
      (fun i_0 => (if ((i * 32) <= i_0 < ((i * 32) + 32)) then aux_0.[
                                                               (i_0 -
                                                               (i * 32))] else 
                  pk.[i_0]))
      );
      (aux_0, aux_1) <@ __gen_chain_inplace_ ((Array32.init
                                              (fun i_0 => pk.[((i * 32) +
                                                              i_0)])
                                              ),
      start, steps, pub_seed, addr);
      pk <-
      (Array2144.init
      (fun i_0 => (if ((i * 32) <= i_0 < ((i * 32) + 32)) then aux_0.[
                                                               (i_0 -
                                                               (i * 32))] else 
                  pk.[i_0]))
      );
      addr <- aux_1;
      i <- (i + 1);
    }
    return (pk, addr);
  }
  proc _wots_pk_from_sig (pk:W8.t Array2144.t, sig_ptr:W64.t,
                          msg:W8.t Array32.t, pub_seed:W8.t Array32.t,
                          addr:W32.t Array8.t) : W8.t Array2144.t *
                                                 W32.t Array8.t = {
    
    (pk, addr) <@ __wots_pk_from_sig (pk, sig_ptr, msg, pub_seed, addr);
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
  proc __memcmp (a:W8.t Array32.t, b:W8.t Array32.t) : W8.t = {
    var acc:W8.t;
    var i:W64.t;
    var t:W8.t;
    acc <- (W8.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      t <- a.[(W64.to_uint i)];
      t <- (t `^` b.[(W64.to_uint i)]);
      acc <- (acc `|` t);
      i <- (i + (W64.of_int 1));
    }
    return acc;
  }
  proc __l_tree (leaf:W8.t Array32.t, wots_pk:W8.t Array2144.t,
                 pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : W8.t Array32.t *
                                                                 W8.t Array2144.t *
                                                                 W32.t Array8.t = {
    var l:W64.t;
    var height:W32.t;
    var parent_nodes:W64.t;
    var i:W64.t;
    var tree_index:W32.t;
    var offset_in:W64.t;
    var bytes:W64.t;
    var buf1:W8.t Array64.t;
    var buf0:W8.t Array32.t;
    var offset_out:W64.t;
    var t:W64.t;
    var tmp:W8.t Array32.t;
    var  _0:W64.t;
    buf0 <- witness;
    buf1 <- witness;
    tmp <- witness;
    l <- (W64.of_int 67);
    height <- (W32.of_int 0);
    (* Erased call to spill *)
    addr <@ __set_tree_height (addr, height);
    while (((W64.of_int 1) \ult l)) {
      parent_nodes <- l;
      parent_nodes <-
      (parent_nodes `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 63))));
      (* Erased call to spill *)
      i <- (W64.of_int 0);
      while ((i \ult parent_nodes)) {
        (* Erased call to spill *)
        tree_index <- (truncateu32 i);
        addr <@ __set_tree_index (addr, tree_index);
        (* Erased call to unspill *)
        offset_in <- (i * (W64.of_int 2));
        offset_in <- (offset_in * (W64.of_int 32));
        bytes <- (W64.of_int (2 * 32));
        (buf1,  _0) <@ __memcpy_u8u8_2_64_2144 (buf1, wots_pk, offset_in,
        bytes);
        (* Erased call to unspill *)
        (buf0, addr) <@ __thash_h (buf0, buf1, pub_seed, addr);
        (* Erased call to unspill *)
        offset_out <- (i * (W64.of_int 32));
        wots_pk <@ __memcpy_u8u8_offset (wots_pk, offset_out, buf0);
        (* Erased call to spill *)
        (* Erased call to unspill *)
        i <- (i + (W64.of_int 1));
      }
      (* Erased call to unspill *)
      t <- l;
      t <- (t `&` (W64.of_int 1));
      if ((t <> (W64.of_int 0))) {
        (* Erased call to unspill *)
        offset_out <- l;
        offset_out <-
        (offset_out `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 63))));
        offset_out <- (offset_out * (W64.of_int 32));
        offset_in <- l;
        offset_in <- (offset_in - (W64.of_int 1));
        offset_in <- (offset_in * (W64.of_int 32));
        wots_pk <@ __nbytes_copy_inplace_2144 (wots_pk, offset_out,
        offset_in);
        (* Erased call to spill *)
        l <- (l `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 63))));
        l <- (l + (W64.of_int 1));
      } else {
        l <- (l `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 63))));
      }
      (* Erased call to unspill *)
      height <- (height + (W32.of_int 1));
      addr <@ __set_tree_height (addr, height);
      (* Erased call to spill *)
    }
    (* Erased call to unspill *)
    tmp <- (Array32.init (fun i_0 => wots_pk.[(0 + i_0)]));
    leaf <@ _x_memcpy_u8u8_32_32 (leaf, tmp);
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
    var aux:W8.t Array32.t;
    var aux_0:W32.t Array8.t;
    var auth_path_ptr:W64.t;
    var t32:W32.t;
    var buffer:W8.t Array64.t;
    var i:W64.t;
    var tree_height:W32.t;
    var thash_in:W8.t Array64.t;
    buffer <- witness;
    thash_in <- witness;
    auth_path_ptr <- _auth_path_ptr;
    (* Erased call to spill *)
    t32 <- leaf_idx;
    t32 <- (t32 `&` (W32.of_int 1));
    if ((t32 <> (W32.of_int 0))) {
      aux <@ _x_memcpy_u8u8_32_32 ((Array32.init
                                   (fun i_0 => buffer.[(32 + i_0)])),
      leaf);
      buffer <-
      (Array64.init
      (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                  buffer.[i_0]))
      );
      aux <@ _x_memcpy_u8u8p ((Array32.init (fun i_0 => buffer.[(0 + i_0)])),
      auth_path_ptr);
      buffer <-
      (Array64.init
      (fun i_0 => (if (0 <= i_0 < (0 + 32)) then aux.[(i_0 - 0)] else 
                  buffer.[i_0]))
      );
    } else {
      buffer <@ _x_memcpy_u8u8_64_32 (buffer, leaf);
      aux <@ _x_memcpy_u8u8p ((Array32.init (fun i_0 => buffer.[(32 + i_0)])),
      auth_path_ptr);
      buffer <-
      (Array64.init
      (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                  buffer.[i_0]))
      );
    }
    auth_path_ptr <- (auth_path_ptr + (W64.of_int 32));
    (* Erased call to spill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (10 - 1)))) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      tree_height <- (truncateu32 i);
      addr <@ __set_tree_height (addr, tree_height);
      (* Erased call to unspill *)
      leaf_idx <-
      (leaf_idx `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 31))));
      addr <@ __set_tree_index (addr, leaf_idx);
      (* Erased call to spill *)
      (* Erased call to unspill *)
      t32 <- leaf_idx;
      t32 <- (t32 `&` (W32.of_int 1));
      if ((t32 <> (W32.of_int 0))) {
        thash_in <-
        (Array64.init
        (fun i_0 => (get8
                    (WArray64.init64
                    (fun i_0 => (copy_64
                                (Array8.init
                                (fun i_0 => (get64
                                            (WArray64.init8
                                            (fun i_0 => buffer.[i_0])) 
                                            i_0))
                                )).[i_0])
                    ) i_0))
        );
        (aux, aux_0) <@ __thash_h ((Array32.init
                                   (fun i_0 => buffer.[(32 + i_0)])),
        thash_in, pub_seed, addr);
        buffer <-
        (Array64.init
        (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                    buffer.[i_0]))
        );
        addr <- aux_0;
        aux <@ _x_memcpy_u8u8p ((Array32.init (fun i_0 => buffer.[(0 + i_0)])
                                ),
        auth_path_ptr);
        buffer <-
        (Array64.init
        (fun i_0 => (if (0 <= i_0 < (0 + 32)) then aux.[(i_0 - 0)] else 
                    buffer.[i_0]))
        );
      } else {
        thash_in <-
        (Array64.init
        (fun i_0 => (get8
                    (WArray64.init64
                    (fun i_0 => (copy_64
                                (Array8.init
                                (fun i_0 => (get64
                                            (WArray64.init8
                                            (fun i_0 => buffer.[i_0])) 
                                            i_0))
                                )).[i_0])
                    ) i_0))
        );
        (aux, aux_0) <@ __thash_h ((Array32.init
                                   (fun i_0 => buffer.[(0 + i_0)])),
        thash_in, pub_seed, addr);
        buffer <-
        (Array64.init
        (fun i_0 => (if (0 <= i_0 < (0 + 32)) then aux.[(i_0 - 0)] else 
                    buffer.[i_0]))
        );
        addr <- aux_0;
        aux <@ _x_memcpy_u8u8p ((Array32.init
                                (fun i_0 => buffer.[(32 + i_0)])),
        auth_path_ptr);
        buffer <-
        (Array64.init
        (fun i_0 => (if (32 <= i_0 < (32 + 32)) then aux.[(i_0 - 32)] else 
                    buffer.[i_0]))
        );
      }
      (* Erased call to spill *)
      auth_path_ptr <- (auth_path_ptr + (W64.of_int 32));
      (* Erased call to unspill *)
      i <- (i + (W64.of_int 1));
    }
    (* Erased call to unspill *)
    addr <@ __set_tree_height (addr, (W32.of_int (10 - 1)));
    leaf_idx <-
    (leaf_idx `>>` (truncateu8 ((W256.of_int 1) `&` (W256.of_int 31))));
    addr <@ __set_tree_index (addr, leaf_idx);
    (* Erased call to unspill *)
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
  proc __new_compute_root (root:W8.t Array32.t, leaf:W8.t Array32.t,
                           leaf_idx:W32.t, _auth_path_ptr:W64.t,
                           pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    var aux:int;
    var aux_0:W8.t Array32.t;
    var k:int;
    var t:W32.t;
    var node:W8.t Array32.t;
    var thash_in:W8.t Array64.t;
    var _ptr:W64.t;
    node <- witness;
    thash_in <- witness;
    (* Erased call to spill *)
    k <- 0;
    while ((k < 10)) {
      addr <@ __set_tree_height (addr, (W32.of_int k));
      t <- leaf_idx;
      t <- (t `>>` (W8.of_int (k + 1)));
      addr <@ __set_tree_index (addr, t);
      t <- leaf_idx;
      t <- (t `>>` (W8.of_int k));
      t <- (t `&` (W32.of_int 1));
      if ((t = (W32.of_int 0))) {
        if ((k = 0)) {
          thash_in <-
          (Array64.init
          (fun i => (if (0 <= i < (0 + 32)) then (Array32.init
                                                 (fun i => (get8
                                                           (WArray32.init64
                                                           (fun i => 
                                                           (copy_64
                                                           (Array4.init
                                                           (fun i => 
                                                           (get64
                                                           (WArray32.init8
                                                           (fun i => 
                                                           leaf.[i])) 
                                                           i)))).[i])) 
                                                           i))
                                                 ).[(i - 0)] else thash_in.[
                                                                  i]))
          );
        } else {
          thash_in <-
          (Array64.init
          (fun i => (if (0 <= i < (0 + 32)) then (Array32.init
                                                 (fun i => (get8
                                                           (WArray32.init64
                                                           (fun i => 
                                                           (copy_64
                                                           (Array4.init
                                                           (fun i => 
                                                           (get64
                                                           (WArray32.init8
                                                           (fun i => 
                                                           node.[i])) 
                                                           i)))).[i])) 
                                                           i))
                                                 ).[(i - 0)] else thash_in.[
                                                                  i]))
          );
        }
        (* Erased call to unspill *)
        _ptr <- _auth_path_ptr;
        _ptr <- (_ptr + (W64.of_int (k * 32)));
        aux_0 <@ _x_memcpy_u8u8p ((Array32.init
                                  (fun i => thash_in.[(32 + i)])),
        _ptr);
        thash_in <-
        (Array64.init
        (fun i => (if (32 <= i < (32 + 32)) then aux_0.[(i - 32)] else 
                  thash_in.[i]))
        );
      } else {
        if ((k = 0)) {
          thash_in <-
          (Array64.init
          (fun i => (if (32 <= i < (32 + 32)) then (Array32.init
                                                   (fun i => (get8
                                                             (WArray32.init64
                                                             (fun i => 
                                                             (copy_64
                                                             (Array4.init
                                                             (fun i => 
                                                             (get64
                                                             (WArray32.init8
                                                             (fun i => 
                                                             leaf.[i])) 
                                                             i)))).[i])) 
                                                             i))
                                                   ).[(i - 32)] else 
                    thash_in.[i]))
          );
        } else {
          thash_in <-
          (Array64.init
          (fun i => (if (32 <= i < (32 + 32)) then (Array32.init
                                                   (fun i => (get8
                                                             (WArray32.init64
                                                             (fun i => 
                                                             (copy_64
                                                             (Array4.init
                                                             (fun i => 
                                                             (get64
                                                             (WArray32.init8
                                                             (fun i => 
                                                             node.[i])) 
                                                             i)))).[i])) 
                                                             i))
                                                   ).[(i - 32)] else 
                    thash_in.[i]))
          );
        }
        (* Erased call to unspill *)
        _ptr <- _auth_path_ptr;
        _ptr <- (_ptr + (W64.of_int (k * 32)));
        aux_0 <@ _x_memcpy_u8u8p ((Array32.init (fun i => thash_in.[(0 + i)])
                                  ),
        _ptr);
        thash_in <-
        (Array64.init
        (fun i => (if (0 <= i < (0 + 32)) then aux_0.[(i - 0)] else thash_in.[
                                                                    i]))
        );
      }
      (* Erased call to unspill *)
      if ((k = (10 - 1))) {
        (* Erased call to unspill *)
        (root, addr) <@ __thash_h (root, thash_in, pub_seed, addr);
        (* Erased call to spill *)
      } else {
        (node, addr) <@ __thash_h (node, thash_in, pub_seed, addr);
      }
      k <- (k + 1);
    }
    (* Erased call to unspill *)
    return (root, addr);
  }
  proc _new_compute_root (root:W8.t Array32.t, leaf:W8.t Array32.t,
                          leaf_idx:W32.t, auth_path_ptr:W64.t,
                          pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    
    (root, addr) <@ __new_compute_root (root, leaf, leaf_idx, auth_path_ptr,
    pub_seed, addr);
    return (root, addr);
  }
  proc __new_compute_root_ (root:W8.t Array32.t, leaf:W8.t Array32.t,
                            leaf_idx:W32.t, auth_path_ptr:W64.t,
                            pub_seed:W8.t Array32.t, addr:W32.t Array8.t) : 
  W8.t Array32.t * W32.t Array8.t = {
    
    root <- root;
    leaf <- leaf;
    leaf_idx <- leaf_idx;
    auth_path_ptr <- auth_path_ptr;
    pub_seed <- pub_seed;
    addr <- addr;
    (root, addr) <@ _new_compute_root (root, leaf, leaf_idx, auth_path_ptr,
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
    (* Erased call to spill *)
    (pk, ots_addr) <@ __wots_pkgen (pk, sk_seed, pub_seed, ots_addr);
    (* Erased call to spill *)
    (* Erased call to unspill *)
    (leaf,  _0, ltree_addr) <@ __l_tree_ (leaf, pk, pub_seed, ltree_addr);
    (* Erased call to unspill *)
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
  proc __set_result (are_equal:W8.t, m_ptr:W64.t, mlen_ptr:W64.t,
                     sm_ptr:W64.t, sm_offset:W64.t) : W64.t = {
    var res_0:W64.t;
    var bytes:W64.t;
    var offset_in:W64.t;
    if ((are_equal <> (W8.of_int 0))) {
      res_0 <- (W64.of_int (- 1));
      bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
      __memset_u8_ptr (m_ptr, bytes, (W8.of_int 0));
      Glob.mem <-
      (storeW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0)))
      (W64.of_int 0));
    } else {
      res_0 <- (W64.of_int 0);
      bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
      offset_in <- sm_offset;
      _x__memcpy_u8pu8p (m_ptr, (W64.of_int 0), sm_ptr, offset_in, bytes);
    }
    return res_0;
  }
  proc __xmssmt_core_sign_open (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                                smlen:W64.t, pk:W8.t Array64.t) : W64.t = {
    var res_0:W64.t;
    var sm_offset:W64.t;
    var pub_root:W8.t Array32.t;
    var pub_seed:W8.t Array32.t;
    var ots_addr:W32.t Array8.t;
    var ltree_addr:W32.t Array8.t;
    var node_addr:W32.t Array8.t;
    var t64:W64.t;
    var idx:W64.t;
    var offset_out:W64.t;
    var offset_in:W64.t;
    var bytes:W64.t;
    var buf:W8.t Array32.t;
    var root:W8.t Array32.t;
    var i:W32.t;
    var idx_leaf:W32.t;
    var wots_pk:W8.t Array2144.t;
    var leaf:W8.t Array32.t;
    var are_equal:W8.t;
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
    pub_root <- (Array32.init (fun i_0 => pk.[(0 + i_0)]));
    pub_seed <- (Array32.init (fun i_0 => pk.[(32 + i_0)]));
    (* Erased call to spill *)
    ots_addr <@ __zero_address_ (ots_addr);
    ltree_addr <@ __zero_address_ (ltree_addr);
    node_addr <@ __zero_address_ (node_addr);
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    ltree_addr <@ __set_type (ltree_addr, (W32.of_int 1));
    node_addr <@ __set_type (node_addr, (W32.of_int 2));
    t64 <- smlen;
    t64 <- (t64 - (W64.of_int 4963));
    Glob.mem <-
    (storeW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))) t64);
    idx <@ __bytes_to_ull_ptr (sm_ptr);
    (* Erased call to spill *)
    offset_out <- (W64.of_int 4963);
    offset_in <- (W64.of_int 4963);
    bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
    _x__memcpy_u8pu8p (m_ptr, offset_out, sm_ptr, offset_in, bytes);
    t64 <- sm_ptr;
    t64 <- (t64 + (W64.of_int 3));
    buf <@ _x_memcpy_u8u8p (buf, t64);
    t64 <- m_ptr;
    t64 <- (t64 + (W64.of_int ((4963 - 32) - (3 * 32))));
    bytes <- (loadW64 Glob.mem (W64.to_uint (mlen_ptr + (W64.of_int 0))));
    root <@ __hash_message (root, buf,
    (Array32.init (fun i_0 => pk.[(0 + i_0)])), idx, t64, bytes);
    t64 <- (W64.of_int (3 + 32));
    sm_offset <- (sm_offset + t64);
    i <- (W32.of_int 0);
    while ((i \ult (W32.of_int 2))) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      idx_leaf <- (W32.of_int ((1 `<<` 10) - 1));
      idx_leaf <- (idx_leaf `&` (truncateu32 idx));
      idx <- (idx `>>` (truncateu8 ((W256.of_int 10) `&` (W256.of_int 63))));
      (* Erased call to spill *)
      ots_addr <@ __set_layer_addr (ots_addr, i);
      ltree_addr <@ __set_layer_addr (ltree_addr, i);
      node_addr <@ __set_layer_addr (node_addr, i);
      ltree_addr <@ __set_tree_addr (ltree_addr, idx);
      ots_addr <@ __set_tree_addr (ots_addr, idx);
      node_addr <@ __set_tree_addr (node_addr, idx);
      ots_addr <@ __set_ots_addr (ots_addr, idx_leaf);
      (* Erased call to unspill *)
      t64 <- sm_ptr;
      t64 <- (t64 + sm_offset);
      root <- root;
      (wots_pk, ots_addr) <@ __wots_pk_from_sig_ (wots_pk, t64, root,
      pub_seed, ots_addr);
      t64 <- sm_offset;
      t64 <- (t64 + (W64.of_int 2144));
      sm_offset <- t64;
      (* Erased call to unspill *)
      ltree_addr <@ __set_ltree_addr (ltree_addr, idx_leaf);
      (* Erased call to unspill *)
      (leaf, wots_pk, ltree_addr) <@ __l_tree_ (leaf, wots_pk, pub_seed,
      ltree_addr);
      (* Erased call to unspill *)
      t64 <- sm_ptr;
      t64 <- (t64 + sm_offset);
      idx_leaf <- idx_leaf;
      root <- root;
      (root, node_addr) <@ __new_compute_root_ (root, leaf, idx_leaf, 
      t64, pub_seed, node_addr);
      t64 <- sm_offset;
      t64 <- (t64 + (W64.of_int (10 * 32)));
      sm_offset <- t64;
      (* Erased call to unspill *)
      i <- (i + (W32.of_int 1));
    }
    (* Erased call to unspill *)
    are_equal <@ __memcmp (root, pub_root);
    (* Erased call to unspill *)
    res_0 <@ __set_result (are_equal, m_ptr, mlen_ptr, sm_ptr, sm_offset);
    return res_0;
  }
  proc _xmssmt_core_sign_open (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                               smlen:W64.t, pk:W8.t Array64.t) : W64.t = {
    var res_0:W64.t;
    res_0 <@ __xmssmt_core_sign_open (m_ptr, mlen_ptr, sm_ptr, smlen, pk);
    return res_0;
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
    return res_0;
  }
  proc __xmss_core_sign_open_ (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                               smlen:W64.t, pk:W8.t Array64.t) : W64.t = {
    var res_0:W64.t;
    m_ptr <- m_ptr;
    mlen_ptr <- mlen_ptr;
    sm_ptr <- sm_ptr;
    smlen <- smlen;
    pk <- pk;
    res_0 <@ _xmssmt_core_sign_open (m_ptr, mlen_ptr, sm_ptr, smlen, pk);
    res_0 <- res_0;
    return res_0;
  }
  proc __treehash_cond (heights:W32.t Array11.t, offset:W64.t) : W8.t = {
    var res_0:W8.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var c1:bool;
    var bc1:W8.t;
    var a:W32.t;
    var b:W32.t;
    var c2:bool;
    var  _0:bool;
    var  _1:bool;
    (_of_, _cf_, _sf_,  _0, _zf_) <- (CMP_64 offset (W64.of_int 2));
    c1 <- (_uGE _of_ _cf_ _sf_ _zf_);
    bc1 <- (SETcc c1);
    if ((bc1 = (W8.of_int 0))) {
      res_0 <- bc1;
    } else {
      a <- heights.[(W64.to_uint (offset - (W64.of_int 1)))];
      b <- heights.[(W64.to_uint (offset - (W64.of_int 2)))];
      (_of_, _cf_, _sf_,  _1, _zf_) <- (CMP_32 a b);
      c2 <- (_EQ _of_ _cf_ _sf_ _zf_);
      res_0 <- (SETcc c2);
    }
    return res_0;
  }
  proc __treehash (root:W8.t Array32.t, sk_seed:W8.t Array32.t,
                   pub_seed:W8.t Array32.t, start_index:W32.t,
                   target_height:W32.t, subtree_addr:W32.t Array8.t) : 
  W8.t Array32.t = {
    var aux:int;
    var offset:W64.t;
    var ots_addr:W32.t Array8.t;
    var ltree_addr:W32.t Array8.t;
    var node_addr:W32.t Array8.t;
    var i:W32.t;
    var upper_bound:W32.t;
    var t32:W32.t;
    var buf:W8.t Array32.t;
    var t64:W64.t;
    var _stack:W8.t Array352.t;
    var heights:W32.t Array11.t;
    var tree_idx:W32.t;
    var u:W32.t;
    var buf2:W8.t Array64.t;
    var cond:W8.t;
    var j:int;
    var  _0:W64.t;
    _stack <- witness;
    buf <- witness;
    buf2 <- witness;
    heights <- witness;
    ltree_addr <- witness;
    node_addr <- witness;
    ots_addr <- witness;
    offset <- (W64.of_int 0);
    (* Erased call to spill *)
    ots_addr <-
    (Array8.init
    (fun i_0 => (get32
                (WArray32.init64
                (fun i_0 => (copy_64
                            (Array4.init
                            (fun i_0 => (get64
                                        (WArray32.init32
                                        (fun i_0 => subtree_addr.[i_0])) 
                                        i_0))
                            )).[i_0])
                ) i_0))
    );
    ltree_addr <-
    (Array8.init
    (fun i_0 => (get32
                (WArray32.init64
                (fun i_0 => (copy_64
                            (Array4.init
                            (fun i_0 => (get64
                                        (WArray32.init32
                                        (fun i_0 => subtree_addr.[i_0])) 
                                        i_0))
                            )).[i_0])
                ) i_0))
    );
    node_addr <-
    (Array8.init
    (fun i_0 => (get32
                (WArray32.init64
                (fun i_0 => (copy_64
                            (Array4.init
                            (fun i_0 => (get64
                                        (WArray32.init32
                                        (fun i_0 => subtree_addr.[i_0])) 
                                        i_0))
                            )).[i_0])
                ) i_0))
    );
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    ltree_addr <@ __set_type (ltree_addr, (W32.of_int 1));
    node_addr <@ __set_type (node_addr, (W32.of_int 2));
    target_height <- target_height;
    i <- (W32.of_int 0);
    upper_bound <- (W32.of_int 1);
    upper_bound <-
    (upper_bound `<<` (truncateu8 (target_height `&` (W32.of_int 31))));
    while ((i \ult upper_bound)) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      t32 <- start_index;
      t32 <- (t32 + i);
      ltree_addr <@ __set_ltree_addr (ltree_addr, t32);
      ots_addr <@ __set_ots_addr (ots_addr, t32);
      (* Erased call to unspill *)
      (buf, ltree_addr, ots_addr) <@ __gen_leaf_wots_ (buf, sk_seed,
      pub_seed, ltree_addr, ots_addr);
      (* Erased call to unspill *)
      t64 <- offset;
      t64 <- (t64 * (W64.of_int 32));
      _stack <@ __memcpy_u8u8_3_352_32 (_stack, buf, t64, 32);
      (* Erased call to unspill *)
      offset <- (offset + (W64.of_int 1));
      heights.[(W64.to_uint (offset - (W64.of_int 1)))] <- (W32.of_int 0);
      (* Erased call to spill *)
      cond <@ __treehash_cond (heights, offset);
      while ((cond = (W8.of_int 1))) {
        (* Erased call to unspill *)
        tree_idx <- start_index;
        tree_idx <- (tree_idx + i);
        u <- heights.[(W64.to_uint (offset - (W64.of_int 1)))];
        u <- (u + (W32.of_int 1));
        tree_idx <- (tree_idx `>>` (truncateu8 (u `&` (W32.of_int 31))));
        node_addr <@ __set_tree_height (node_addr,
        heights.[(W64.to_uint (offset - (W64.of_int 1)))]);
        node_addr <@ __set_tree_index (node_addr, tree_idx);
        (* Erased call to unspill *)
        t64 <- offset;
        t64 <- (t64 - (W64.of_int 2));
        t64 <- (t64 * (W64.of_int 32));
        (buf2,  _0) <@ __memcpy_u8u8_2_64_352 (buf2, _stack, t64,
        (W64.of_int (2 * 32)));
        (* Erased call to unspill *)
        (buf, node_addr) <@ __thash_h_ (buf, buf2, pub_seed, node_addr);
        (* Erased call to unspill *)
        t64 <- offset;
        t64 <- (t64 - (W64.of_int 2));
        t64 <- (t64 * (W64.of_int 32));
        _stack <@ __memcpy_u8u8_3_352_32 (_stack, buf, t64, 32);
        (* Erased call to unspill *)
        offset <- (offset - (W64.of_int 1));
        heights.[(W64.to_uint (offset - (W64.of_int 1)))] <-
        (heights.[(W64.to_uint (offset - (W64.of_int 1)))] + (W32.of_int 1));
        (* Erased call to spill *)
        cond <@ __treehash_cond (heights, offset);
      }
      (* Erased call to unspill *)
      i <- (i + (W32.of_int 1));
    }
    (* Erased call to unspill *)
    j <- 0;
    while ((j < 32)) {
      root.[j] <- _stack.[j];
      j <- (j + 1);
    }
    return root;
  }
  proc _treehash (node:W8.t Array32.t, sk_seed:W8.t Array32.t,
                  pub_seed:W8.t Array32.t, s:W32.t, t:W32.t,
                  subtree_addr:W32.t Array8.t) : W8.t Array32.t = {
    
    node <@ __treehash (node, sk_seed, pub_seed, s, t, subtree_addr);
    return node;
  }
  proc __treehash_ (node:W8.t Array32.t, sk_seed:W8.t Array32.t,
                    pub_seed:W8.t Array32.t, s:W32.t, t:W32.t,
                    subtree_addr:W32.t Array8.t) : W8.t Array32.t = {
    
    node <- node;
    sk_seed <- sk_seed;
    pub_seed <- pub_seed;
    s <- s;
    t <- t;
    subtree_addr <- subtree_addr;
    node <@ _treehash (node, sk_seed, pub_seed, s, t, subtree_addr);
    node <- node;
    return node;
  }
  proc __build_auth_path (auth_path:W8.t Array320.t, sk_seed:W8.t Array32.t,
                          pub_seed:W8.t Array32.t, i:W32.t,
                          addr:W32.t Array8.t) : W8.t Array320.t = {
    var aux:int;
    var j:int;
    var k:W32.t;
    var node:W8.t Array32.t;
    node <- witness;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 10)) {
      (* Erased call to unspill *)
      k <- (i `>>` (W8.of_int j));
      k <- (k `^` (W32.of_int 1));
      k <- (k `<<` (W8.of_int j));
      (* Erased call to unspill *)
      node <- (Array32.init (fun i_0 => auth_path.[((j * 32) + i_0)]));
      (* Erased call to unspill *)
      node <@ __treehash_ (node, sk_seed, pub_seed, k, (W32.of_int j), addr);
      (* Erased call to unspill *)
      auth_path <-
      (Array320.init
      (fun i_0 => (if ((j * 32) <= i_0 < ((j * 32) + 32)) then node.[
                                                               (i_0 -
                                                               (j * 32))] else 
                  auth_path.[i_0]))
      );
      (* Erased call to spill *)
      j <- (j + 1);
    }
    return auth_path;
  }
  proc __tree_sig (sig:W8.t Array2464.t, m:W8.t Array32.t,
                   sk:W8.t Array131.t, idx_sig:W32.t, addr:W32.t Array8.t) : 
  W8.t Array2464.t * W32.t Array8.t = {
    var aux:int;
    var pub_seed:W8.t Array32.t;
    var sk_seed:W8.t Array32.t;
    var auth_path:W8.t Array320.t;
    var sig_ots:W8.t Array2144.t;
    var i:int;
    auth_path <- witness;
    pub_seed <- witness;
    sig_ots <- witness;
    sk_seed <- witness;
    pub_seed <- (Array32.init (fun i_0 => sk.[((3 + (3 * 32)) + i_0)]));
    sk_seed <- (Array32.init (fun i_0 => sk.[(3 + i_0)]));
    addr.[4] <- (W32.of_int 0);
    (* Erased call to spill *)
    auth_path <@ __build_auth_path (auth_path, sk_seed, pub_seed, idx_sig,
    addr);
    (* Erased call to unspill *)
    addr <@ __set_type (addr, (W32.of_int 0));
    addr <@ __set_ots_addr (addr, idx_sig);
    (* Erased call to unspill *)
    (sig_ots, addr) <@ __wots_sign_ (sig_ots, m, sk_seed, pub_seed, addr);
    (* Erased call to unspill *)
    i <- 0;
    while ((i < 2144)) {
      sig.[i] <- sig_ots.[i];
      i <- (i + 1);
    }
    aux <- (10 * 32);
    i <- 0;
    while ((i < aux)) {
      sig.[((67 * 32) + i)] <- auth_path.[i];
      i <- (i + 1);
    }
    return (sig, addr);
  }
  proc _tree_sig (sig:W8.t Array2464.t, m:W8.t Array32.t, sk:W8.t Array131.t,
                  idx_sig:W32.t, addr:W32.t Array8.t) : W8.t Array2464.t *
                                                        W32.t Array8.t = {
    
    (sig, addr) <@ __tree_sig (sig, m, sk, idx_sig, addr);
    return (sig, addr);
  }
  proc __tree_sig_ (sig:W8.t Array2464.t, m:W8.t Array32.t,
                    sk:W8.t Array131.t, idx_sig:W32.t, addr:W32.t Array8.t) : 
  W8.t Array2464.t * W32.t Array8.t = {
    
    sig <- sig;
    m <- m;
    sk <- sk;
    idx_sig <- idx_sig;
    addr <- addr;
    (sig, addr) <@ __tree_sig (sig, m, sk, idx_sig, addr);
    sig <- sig;
    addr <- addr;
    return (sig, addr);
  }
  proc __xmssmt_core_seed_keypair (pk:W8.t Array64.t, sk:W8.t Array131.t,
                                   seed:W8.t Array96.t) : W8.t Array64.t *
                                                          W8.t Array131.t = {
    var top_tree_addr:W32.t Array8.t;
    var idx:W8.t Array3.t;
    var buf0:W8.t Array64.t;
    var buf1:W8.t Array64.t;
    var bufn0:W8.t Array32.t;
    var bufn1:W8.t Array32.t;
    var root:W8.t Array32.t;
    buf0 <- witness;
    buf1 <- witness;
    bufn0 <- witness;
    bufn1 <- witness;
    idx <- witness;
    root <- witness;
    top_tree_addr <- witness;
    top_tree_addr <@ __zero_address_ (top_tree_addr);
    top_tree_addr <@ __set_layer_addr (top_tree_addr, (W32.of_int (2 - 1)));
    idx <- (Array3.init (fun i => sk.[(0 + i)]));
    idx <@ __memset_zero_u8 (idx);
    sk <-
    (Array131.init
    (fun i => (if (0 <= i < (0 + 3)) then idx.[(i - 0)] else sk.[i])));
    buf0 <- (Array64.init (fun i => sk.[(3 + i)]));
    buf1 <- (Array64.init (fun i => seed.[(0 + i)]));
    buf0 <@ _x_memcpy_u8u8_64_64 (buf0, buf1);
    sk <-
    (Array131.init
    (fun i => (if (3 <= i < (3 + 64)) then buf0.[(i - 3)] else sk.[i])));
    bufn0 <- (Array32.init (fun i => sk.[((3 + (3 * 32)) + i)]));
    bufn1 <- (Array32.init (fun i => seed.[((2 * 32) + i)]));
    bufn0 <@ _x_memcpy_u8u8_32_32 (bufn0, bufn1);
    sk <-
    (Array131.init
    (fun i => (if ((3 + (3 * 32)) <= i < ((3 + (3 * 32)) + 32)) then 
              bufn0.[(i - (3 + (3 * 32)))] else sk.[i]))
    );
    bufn0 <- (Array32.init (fun i => pk.[(32 + i)]));
    bufn1 <- (Array32.init (fun i => sk.[((3 + (3 * 32)) + i)]));
    bufn0 <@ _x_memcpy_u8u8_32_32 (bufn0, bufn1);
    pk <-
    (Array64.init
    (fun i => (if (32 <= i < (32 + 32)) then bufn0.[(i - 32)] else pk.[i])));
    bufn0 <- (Array32.init (fun i => sk.[(3 + i)]));
    bufn1 <- (Array32.init (fun i => pk.[(32 + i)]));
    (* Erased call to spill *)
    root <@ __treehash_ (root, bufn0, bufn1, (W32.of_int 0), (W32.of_int 10),
    top_tree_addr);
    (* Erased call to unspill *)
    pk <@ __nbytes_copy_offset_64_32 (pk, (W64.of_int 0), root,
    (W64.of_int 0));
    sk <@ __nbytes_copy_offset_131_32 (sk, (W64.of_int (3 + (2 * 32))), 
    root, (W64.of_int 0));
    return (pk, sk);
  }
  proc __xmssmt_core_keypair (pk:W8.t Array64.t, sk:W8.t Array131.t) : 
  W8.t Array64.t * W8.t Array131.t = {
    var seed:W8.t Array96.t;
    var seed_p:W8.t Array96.t;
    seed <- witness;
    seed_p <- witness;
    seed_p <- seed;
    seed_p <@ SC.randombytes_96 (seed_p);
    (pk, sk) <@ __xmssmt_core_seed_keypair (pk, sk, seed_p);
    return (pk, sk);
  }
  proc _xmssmt_core_keypair (pk:W8.t Array64.t, sk:W8.t Array131.t) : 
  W8.t Array64.t * W8.t Array131.t = {
    
    (pk, sk) <@ __xmssmt_core_keypair (pk, sk);
    return (pk, sk);
  }
  proc __xmssmt_core_keypair_ (pk:W8.t Array64.t, sk:W8.t Array131.t) : 
  W8.t Array64.t * W8.t Array131.t = {
    
    pk <- pk;
    sk <- sk;
    (pk, sk) <@ _xmssmt_core_keypair (pk, sk);
    pk <- pk;
    sk <- sk;
    return (pk, sk);
  }
  proc __xmssmt_core_sign (sk:W8.t Array131.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                           m_ptr:W64.t, mlen:W64.t) : W8.t Array131.t * W64.t = {
    var aux_3:int;
    var aux_0:W8.t Array3.t;
    var aux:W8.t Array128.t;
    var aux_1:W8.t Array2464.t;
    var aux_2:W32.t Array8.t;
    var r:W64.t;
    var exit_0:W8.t;
    var ots_addr:W32.t Array8.t;
    var t64:W64.t;
    var idx:W64.t;
    var idx_bytes:W8.t Array3.t;
    var signature:W8.t Array4963.t;
    var index_bytes:W8.t Array32.t;
    var sk_prf:W8.t Array32.t;
    var buf:W8.t Array32.t;
    var pub_root:W8.t Array32.t;
    var mhash:W8.t Array32.t;
    var idx_tree:W64.t;
    var idx_leaf:W32.t;
    var sk_seed:W8.t Array32.t;
    var pub_seed:W8.t Array32.t;
    var root:W8.t Array32.t;
    var i:int;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    buf <- witness;
    idx_bytes <- witness;
    index_bytes <- witness;
    mhash <- witness;
    ots_addr <- witness;
    pub_root <- witness;
    pub_seed <- witness;
    root <- witness;
    signature <- witness;
    sk_prf <- witness;
    sk_seed <- witness;
    exit_0 <- (W8.of_int 0);
    ots_addr <@ __zero_address_ (ots_addr);
    ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
    _x__memcpy_u8pu8p (sm_ptr, (W64.of_int 4963), m_ptr, (W64.of_int 0),
    mlen);
    t64 <- mlen;
    t64 <- (t64 + (W64.of_int 4963));
    Glob.mem <-
    (storeW64 Glob.mem (W64.to_uint (smlen_ptr + (W64.of_int 0))) t64);
    (* Erased call to spill *)
    idx_bytes <- (Array3.init (fun i_0 => sk.[(0 + i_0)]));
    idx <@ __bytes_to_ull (idx_bytes);
    if (((W64.of_int ((1 `<<` 20) - 1)) \ule idx)) {
      idx_bytes <@ __memset_u8_3 (idx_bytes, (W8.of_int 255));
      sk <-
      (Array131.init
      (fun i_0 => (if (0 <= i_0 < (0 + 3)) then idx_bytes.[(i_0 - 0)] else 
                  sk.[i_0]))
      );
      aux <@ __memset_u8_128 ((Array128.init (fun i_0 => sk.[(3 + i_0)])),
      (W8.of_int 0));
      sk <-
      (Array131.init
      (fun i_0 => (if (3 <= i_0 < (3 + 128)) then aux.[(i_0 - 3)] else 
                  sk.[i_0]))
      );
      if (((W64.of_int ((1 `<<` 20) - 1)) \ult idx)) {
        exit_0 <- (W8.of_int 1);
        r <- (W64.of_int (- 2));
      } else {
        if (((idx = (W64.of_int ((1 `<<` 20) - 1))) /\ (20 = 64))) {
          exit_0 <- (W8.of_int 1);
          r <- (W64.of_int (- 2));
        } else {
          
        }
      }
      (* Erased call to spill *)
    } else {
      
    }
    if ((exit_0 <> (W8.of_int 1))) {
      signature <-
      (Array4963.init
      (fun i_0 => (if (0 <= i_0 < (0 + 3)) then (copy_8 idx_bytes).[(i_0 - 0)] else 
                  signature.[i_0]))
      );
      (* Erased call to spill *)
      t64 <- idx;
      t64 <- (t64 + (W64.of_int 1));
      aux_0 <@ __ull_to_bytes_3 ((Array3.init (fun i_0 => sk.[(0 + i_0)])),
      t64);
      sk <-
      (Array131.init
      (fun i_0 => (if (0 <= i_0 < (0 + 3)) then aux_0.[(i_0 - 0)] else 
                  sk.[i_0]))
      );
      (* Erased call to spill *)
      index_bytes <@ __ull_to_bytes_32 (index_bytes, idx);
      sk_prf <- (Array32.init (fun i_0 => sk.[((3 + 32) + i_0)]));
      buf <@ __prf_ (buf, index_bytes, sk_prf);
      signature <-
      (Array4963.init
      (fun i_0 => (if (3 <= i_0 < (3 + 32)) then (copy_8 buf).[(i_0 - 3)] else 
                  signature.[i_0]))
      );
      (* Erased call to unspill *)
      pub_root <- (Array32.init (fun i_0 => sk.[((3 + (2 * 32)) + i_0)]));
      t64 <- sm_ptr;
      t64 <- (t64 + (W64.of_int ((4963 - 32) - (3 * 32))));
      mhash <@ __hash_message (mhash,
      (Array32.init (fun i_0 => signature.[(3 + i_0)])), pub_root, idx, 
      t64, mlen);
      ots_addr <@ __set_type (ots_addr, (W32.of_int 0));
      ots_addr <@ __set_layer_addr (ots_addr, (W32.of_int 0));
      (* Erased call to unspill *)
      idx_tree <- idx;
      idx_tree <- (idx_tree `>>` (W8.of_int 10));
      idx_leaf <- (W32.of_int ((1 `<<` 10) - 1));
      idx_leaf <- (idx_leaf `&` (truncateu32 idx));
      (* Erased call to spill *)
      ots_addr <@ __set_tree_addr (ots_addr, idx_tree);
      (* Erased call to unspill *)
      (aux_1, aux_2) <@ __tree_sig_ ((Array2464.init
                                     (fun i_0 => signature.[((3 + 32) + i_0)])
                                     ),
      mhash, sk, idx_leaf, ots_addr);
      signature <-
      (Array4963.init
      (fun i_0 => (if ((3 + 32) <= i_0 < ((3 + 32) + 2464)) then aux_1.[
                                                                 (i_0 -
                                                                 (3 + 32))] else 
                  signature.[i_0]))
      );
      ots_addr <- aux_2;
      i <- 1;
      while ((i < 2)) {
        (* Erased call to unspill *)
        sk_seed <- (Array32.init (fun i_0 => sk.[(3 + i_0)]));
        pub_seed <- (Array32.init (fun i_0 => sk.[((3 + (3 * 32)) + i_0)]));
        ots_addr.[4] <- (W32.of_int 0);
        root <@ __treehash_ (root, sk_seed, pub_seed, (W32.of_int 0),
        (W32.of_int 10), ots_addr);
        (* Erased call to unspill *)
        idx_tree <- (idx_tree `>>` (W8.of_int 10));
        idx_leaf <- (W32.of_int ((1 `<<` 10) - 1));
        idx_leaf <- (idx_leaf `&` (truncateu32 idx_tree));
        (* Erased call to spill *)
        ots_addr <@ __set_layer_addr (ots_addr, (W32.of_int i));
        ots_addr <@ __set_tree_addr (ots_addr, idx_tree);
        (* Erased call to unspill *)
        (aux_1, aux_2) <@ __tree_sig_ ((Array2464.init
                                       (fun i_0 => signature.[(((3 + 32) +
                                                               (i * 2464)) +
                                                              i_0)])
                                       ),
        root, sk, idx_leaf, ots_addr);
        signature <-
        (Array4963.init
        (fun i_0 => (if (((3 + 32) + (i * 2464)) <= i_0 < (((3 + 32) +
                                                           (i * 2464)) +
                                                          2464)) then 
                    aux_1.[(i_0 - ((3 + 32) + (i * 2464)))] else signature.[
                                                                 i_0]))
        );
        ots_addr <- aux_2;
        i <- (i + 1);
      }
      (* Erased call to unspill *)
      i <- 0;
      while ((i < 4963)) {
        Glob.mem <-
        (storeW8 Glob.mem (W64.to_uint (sm_ptr + (W64.of_int i)))
        signature.[i]);
        i <- (i + 1);
      }
      (_of_, _cf_, _sf_,  _0, _zf_, r) <- (set0_64);
    } else {
      
    }
    (* Erased call to unspill *)
    return (sk, r);
  }
  proc _xmssmt_core_sign (sk:W8.t Array131.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                          m_ptr:W64.t, mlen:W64.t) : W8.t Array131.t * W64.t = {
    var r:W64.t;
    (sk, r) <@ __xmssmt_core_sign (sk, sm_ptr, smlen_ptr, m_ptr, mlen);
    return (sk, r);
  }
  proc __xmssmt_core_sign_ (sk:W8.t Array131.t, sm_ptr:W64.t,
                            smlen_ptr:W64.t, m_ptr:W64.t, mlen:W64.t) : 
  W8.t Array131.t * W64.t = {
    var r:W64.t;
    sk <- sk;
    sm_ptr <- sm_ptr;
    smlen_ptr <- smlen_ptr;
    m_ptr <- m_ptr;
    mlen <- mlen;
    (sk, r) <@ _xmssmt_core_sign (sk, sm_ptr, smlen_ptr, m_ptr, mlen);
    sk <- sk;
    r <- r;
    return (sk, r);
  }
  proc __xmss_keypair (pk:W8.t Array68.t, sk:W8.t Array135.t) : W8.t Array68.t *
                                                                W8.t Array135.t = {
    var aux:W8.t Array64.t;
    var aux_0:W8.t Array131.t;
    var oid:W32.t;
    oid <- (W32.of_int 1);
    oid <- (BSWAP_32 oid);
    pk <-
    (Array68.init
    (WArray68.get8 (WArray68.set32 (WArray68.init8 (fun i => pk.[i])) 0 oid))
    );
    sk <-
    (Array135.init
    (WArray135.get8
    (WArray135.set32 (WArray135.init8 (fun i => sk.[i])) 0 oid)));
    (aux, aux_0) <@ __xmssmt_core_keypair_ ((Array64.init
                                            (fun i => pk.[(4 + i)])),
    (Array131.init (fun i => sk.[(4 + i)])));
    pk <-
    (Array68.init
    (fun i => (if (4 <= i < (4 + 64)) then aux.[(i - 4)] else pk.[i])));
    sk <-
    (Array135.init
    (fun i => (if (4 <= i < (4 + 131)) then aux_0.[(i - 4)] else sk.[i])));
    return (pk, sk);
  }
  proc __xmssmt_keypair (pk:W8.t Array68.t, sk:W8.t Array135.t) : W8.t Array68.t *
                                                                  W8.t Array135.t = {
    var aux:W8.t Array64.t;
    var aux_0:W8.t Array131.t;
    var oid:W32.t;
    oid <- (W32.of_int 1);
    oid <- (BSWAP_32 oid);
    pk <-
    (Array68.init
    (WArray68.get8 (WArray68.set32 (WArray68.init8 (fun i => pk.[i])) 0 oid))
    );
    sk <-
    (Array135.init
    (WArray135.get8
    (WArray135.set32 (WArray135.init8 (fun i => sk.[i])) 0 oid)));
    (aux, aux_0) <@ __xmssmt_core_keypair_ ((Array64.init
                                            (fun i => pk.[(4 + i)])),
    (Array131.init (fun i => sk.[(4 + i)])));
    pk <-
    (Array68.init
    (fun i => (if (4 <= i < (4 + 64)) then aux.[(i - 4)] else pk.[i])));
    sk <-
    (Array135.init
    (fun i => (if (4 <= i < (4 + 131)) then aux_0.[(i - 4)] else sk.[i])));
    return (pk, sk);
  }
  proc __xmss_sign (sk:W8.t Array135.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                    m_ptr:W64.t, mlen:W64.t) : W8.t Array135.t * W64.t = {
    var aux_0:W64.t;
    var aux:W8.t Array131.t;
    var res_0:W64.t;
    (aux, aux_0) <@ __xmssmt_core_sign ((Array131.init
                                        (fun i => sk.[(4 + i)])),
    sm_ptr, smlen_ptr, m_ptr, mlen);
    sk <-
    (Array135.init
    (fun i => (if (4 <= i < (4 + 131)) then aux.[(i - 4)] else sk.[i])));
    res_0 <- aux_0;
    return (sk, res_0);
  }
  proc __xmssmt_sign (sk:W8.t Array135.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                      m_ptr:W64.t, mlen:W64.t) : W8.t Array135.t * W64.t = {
    var aux_0:W64.t;
    var aux:W8.t Array131.t;
    var res_0:W64.t;
    (aux, aux_0) <@ __xmssmt_core_sign ((Array131.init
                                        (fun i => sk.[(4 + i)])),
    sm_ptr, smlen_ptr, m_ptr, mlen);
    sk <-
    (Array135.init
    (fun i => (if (4 <= i < (4 + 131)) then aux.[(i - 4)] else sk.[i])));
    res_0 <- aux_0;
    return (sk, res_0);
  }
  proc __xmss_sign_open (pk:W8.t Array68.t, m_ptr:W64.t, mlen_ptr:W64.t,
                         sm_ptr:W64.t, smlen:W64.t) : W64.t = {
    var res_0:W64.t;
    res_0 <@ __xmssmt_core_sign_open_ (m_ptr, mlen_ptr, sm_ptr, smlen,
    (Array64.init (fun i => pk.[(4 + i)])));
    return res_0;
  }
  proc __xmssmt_sign_open (pk:W8.t Array68.t, m_ptr:W64.t, mlen_ptr:W64.t,
                           sm_ptr:W64.t, smlen:W64.t) : W64.t = {
    var res_0:W64.t;
    res_0 <@ __xmssmt_core_sign_open_ (m_ptr, mlen_ptr, sm_ptr, smlen,
    (Array64.init (fun i => pk.[(4 + i)])));
    return res_0;
  }
  proc xmss_keypair_jazz (pk:W8.t Array68.t, sk:W8.t Array135.t) : W8.t Array68.t *
                                                                   W8.t Array135.t *
                                                                   W64.t = {
    var res_0:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    (pk, sk) <@ __xmss_keypair (pk, sk);
    (_of_, _cf_, _sf_,  _0, _zf_, res_0) <- (set0_64);
    return (pk, sk, res_0);
  }
  proc xmssmt_keypair_jazz (pk:W8.t Array68.t, sk:W8.t Array135.t) : 
  W8.t Array68.t * W8.t Array135.t * W64.t = {
    var res_0:W64.t;
    var _of_:bool;
    var _cf_:bool;
    var _sf_:bool;
    var _zf_:bool;
    var  _0:bool;
    (pk, sk) <@ __xmssmt_keypair (pk, sk);
    (_of_, _cf_, _sf_,  _0, _zf_, res_0) <- (set0_64);
    return (pk, sk, res_0);
  }
  proc xmss_sign_jazz (sk:W8.t Array135.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                       m_ptr:W64.t, mlen:W64.t) : W8.t Array135.t * W64.t = {
    var res_0:W64.t;
    (sk, res_0) <@ __xmss_sign (sk, sm_ptr, smlen_ptr, m_ptr, mlen);
    return (sk, res_0);
  }
  proc xmssmt_sign_jazz (sk:W8.t Array135.t, sm_ptr:W64.t, smlen_ptr:W64.t,
                         m_ptr:W64.t, mlen:W64.t) : W8.t Array135.t * W64.t = {
    var res_0:W64.t;
    (sk, res_0) <@ __xmssmt_sign (sk, sm_ptr, smlen_ptr, m_ptr, mlen);
    return (sk, res_0);
  }
  proc xmss_sign_open_jazz (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                            smlen:W64.t, pk:W8.t Array68.t) : W64.t = {
    var res_0:W64.t;
    res_0 <@ __xmss_sign_open (pk, m_ptr, mlen_ptr, sm_ptr, smlen);
    return res_0;
  }
  proc xmssmt_sign_open_jazz (m_ptr:W64.t, mlen_ptr:W64.t, sm_ptr:W64.t,
                              smlen:W64.t, pk:W8.t Array68.t) : W64.t = {
    var res_0:W64.t;
    res_0 <@ __xmssmt_sign_open (pk, m_ptr, mlen_ptr, sm_ptr, smlen);
    return res_0;
  }
}.
