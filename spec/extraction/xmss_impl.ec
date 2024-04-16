require import AllCore IntDiv CoreMap List Distr.
from Jasmin require import JModel_x86.
import SLH64.


require import Array2 Array3 Array4 Array8 Array32 Array64 Array67 Array96
               Array128 Array2144.
require import WArray2 WArray4 WArray12 WArray32 WArray64 WArray96 WArray128
               WArray256 WArray268 WArray2144.

abbrev sHA256_K = Array64.of_list witness [W32.of_int 1116352408;
W32.of_int 1899447441; W32.of_int (-1245643825); W32.of_int (-373957723);
W32.of_int 961987163; W32.of_int 1508970993; W32.of_int (-1841331548);
W32.of_int (-1424204075); W32.of_int (-670586216); W32.of_int 310598401;
W32.of_int 607225278; W32.of_int 1426881987; W32.of_int 1925078388;
W32.of_int (-2132889090); W32.of_int (-1680079193); W32.of_int (-1046744716);
W32.of_int (-459576895); W32.of_int (-272742522); W32.of_int 264347078;
W32.of_int 604807628; W32.of_int 770255983; W32.of_int 1249150122;
W32.of_int 1555081692; W32.of_int 1996064986; W32.of_int (-1740746414);
W32.of_int (-1473132947); W32.of_int (-1341970488); W32.of_int (-1084653625);
W32.of_int (-958395405); W32.of_int (-710438585); W32.of_int 113926993;
W32.of_int 338241895; W32.of_int 666307205; W32.of_int 773529912;
W32.of_int 1294757372; W32.of_int 1396182291; W32.of_int 1695183700;
W32.of_int 1986661051; W32.of_int (-2117940946); W32.of_int (-1838011259);
W32.of_int (-1564481375); W32.of_int (-1474664885); W32.of_int (-1035236496);
W32.of_int (-949202525); W32.of_int (-778901479); W32.of_int (-694614492);
W32.of_int (-200395387); W32.of_int 275423344; W32.of_int 430227734;
W32.of_int 506948616; W32.of_int 659060556; W32.of_int 883997877;
W32.of_int 958139571; W32.of_int 1322822218; W32.of_int 1537002063;
W32.of_int 1747873779; W32.of_int 1955562222; W32.of_int 2024104815;
W32.of_int (-2067236844); W32.of_int (-1933114872); W32.of_int (-1866530822);
W32.of_int (-1538233109); W32.of_int (-1090935817); W32.of_int (-965641998)].


module M = {
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
    return (h);
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
    return (h);
  }
  
  proc __SHR_ref (x:W32.t, c:int) : W32.t = {
    
    var r:W32.t;
    
    r <- x;
    r <- (r `>>` (W8.of_int c));
    return (r);
  }
  
  proc __ROTR_ref (x:W32.t, c:int) : W32.t = {
    
    var r:W32.t;
    var  _0:bool;
    var  _1:bool;
    
    r <- x;
    ( _0,  _1, r) <- ROR_32 r (W8.of_int c);
    return (r);
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
    return (r);
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
    return (r);
  }
  
  proc __BSIG0_ref (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var s:W32.t;
    
    r <@ __ROTR_ref (x, 2);
    s <@ __ROTR_ref (x, 13);
    r <- (r `^` s);
    s <@ __ROTR_ref (x, 22);
    r <- (r `^` s);
    return (r);
  }
  
  proc __BSIG1_ref (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var s:W32.t;
    
    r <@ __ROTR_ref (x, 6);
    s <@ __ROTR_ref (x, 11);
    r <- (r `^` s);
    s <@ __ROTR_ref (x, 25);
    r <- (r `^` s);
    return (r);
  }
  
  proc __SSIG0_ref (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var s:W32.t;
    
    r <@ __ROTR_ref (x, 7);
    s <@ __ROTR_ref (x, 18);
    r <- (r `^` s);
    s <@ __SHR_ref (x, 3);
    r <- (r `^` s);
    return (r);
  }
  
  proc __SSIG1_ref (x:W32.t) : W32.t = {
    
    var r:W32.t;
    var s:W32.t;
    
    r <@ __ROTR_ref (x, 17);
    s <@ __ROTR_ref (x, 19);
    r <- (r `^` s);
    s <@ __SHR_ref (x, 10);
    r <- (r `^` s);
    return (r);
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
    return (w);
  }
  
  proc _blocks_1_ref (_H:W32.t Array8.t, sblocks:W32.t Array32.t,
                      nblocks:W64.t) : W32.t Array8.t * W32.t Array32.t = {
    var aux: int;
    
    var kp:W32.t Array64.t;
    var hp:W32.t Array8.t;
    var i:W64.t;
    var h:W32.t Array8.t;
    var s_i:W64.t;
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
      s_i <- i;
      oblocks <- (i `<<` (W8.of_int 4));
      t <- 0;
      while (t < 16) {
        v <- sblocks.[(W64.to_uint (oblocks + (W64.of_int t)))];
        v <- BSWAP_32 v;
        w.[t] <- v;
        t <- t + 1;
      }
      s_sblocks <- sblocks;
      t <- 16;
      while (t < 64) {
        w <@ __Wt_ref (w, t);
        t <- t + 1;
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
      i <- s_i;
      i <- (i + (W64.of_int 1));
    }
    _H <- h;
    return (_H, sblocks);
  }
  
  proc __store_ref_array (out:W8.t Array32.t, h:W32.t Array8.t) : W8.t Array32.t = {
    var aux: int;
    
    var i:int;
    var v:W32.t;
    
    i <- 0;
    while (i < 8) {
      v <- h.[i];
      v <- BSWAP_32 v;
      out <-
      Array32.init
      (WArray32.get8 (WArray32.set32 (WArray32.init8 (fun i_0 => (out).[i_0])) i (v)));
      i <- i + 1;
    }
    return (out);
  }
  
  proc _blocks_0_ref_128 (_H:W32.t Array8.t, in_0:W8.t Array128.t) : 
  W32.t Array8.t * W64.t = {
    var aux: int;
    
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
        while (t < 16) {
          v <-
          (get32_direct (WArray128.init8 (fun i => (in_0).[i]))
          (W64.to_uint (offset + (W64.of_int (4 * t)))));
          v <- BSWAP_32 v;
          w.[t] <- v;
          t <- t + 1;
        }
        (* Erased call to spill *)
        t <- 16;
        while (t < 64) {
          w <@ __Wt_ref (w, t);
          t <- t + 1;
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
    var aux: int;
    
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
        while (t < 16) {
          v <-
          (get32_direct (WArray96.init8 (fun i => (in_0).[i]))
          (W64.to_uint (offset + (W64.of_int (4 * t)))));
          v <- BSWAP_32 v;
          w.[t] <- v;
          t <- t + 1;
        }
        (* Erased call to spill *)
        t <- 16;
        while (t < 64) {
          w <@ __Wt_ref (w, t);
          t <- t + 1;
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
    var aux: int;
    
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
    while (k < 32) {
      sblocks.[k] <- (truncateu32 i);
      k <- k + 1;
    }
    
    while ((i \ult inlen)) {
      index <- offset;
      index <- (index + i);
      v <- in_0.[(W64.to_uint index)];
      sblocks <-
      Array32.init
      (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) (v)));
      i <- (i + (W64.of_int 1));
    }
    sblocks <-
    Array32.init
    (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) ((W8.of_int 128))));
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
      Array32.init
      (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) ((truncateu8 bits))));
      bits <- (bits `>>` (W8.of_int 8));
      i <- (i - (W64.of_int 1));
    }
    return (sblocks, nblocks);
  }
  
  proc __lastblocks_ref_96 (in_0:W8.t Array96.t, inlen:W64.t, offset:W64.t,
                            bits:W64.t) : W32.t Array32.t * W64.t = {
    var aux: int;
    
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
    while (k < 32) {
      sblocks.[k] <- (truncateu32 i);
      k <- k + 1;
    }
    
    while ((i \ult inlen)) {
      index <- offset;
      index <- (index + i);
      v <- in_0.[(W64.to_uint index)];
      sblocks <-
      Array32.init
      (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) (v)));
      i <- (i + (W64.of_int 1));
    }
    sblocks <-
    Array32.init
    (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) ((W8.of_int 128))));
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
      Array32.init
      (WArray128.get32 (WArray128.set8 (WArray128.init32 (fun i_0 => (sblocks).[i_0])) (W64.to_uint i) ((truncateu8 bits))));
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
    return (out);
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
    return (out);
  }
  
  proc __core_hash_128 (out:W8.t Array32.t, in_0:W8.t Array128.t) : W8.t Array32.t = {
    
    
    
    out <@ __sha256_128 (out, in_0);
    return (out);
  }
  
  proc __core_hash_96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    
    
    out <@ __sha256_96 (out, in_0);
    return (out);
  }
  
  proc _core_hash_96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    
    
    out <@ __core_hash_96 (out, in_0);
    return (out);
  }
  
  proc __core_hash__96 (out:W8.t Array32.t, in_0:W8.t Array96.t) : W8.t Array32.t = {
    
    
    
    in_0 <- in_0;
    out <- out;
    out <@ _core_hash_96 (out, in_0);
    out <- out;
    return (out);
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
  
  proc _memcpy_u8u8_96_32 (out:W8.t Array96.t, offset:W64.t,
                           in_0:W8.t Array32.t) : W8.t Array96.t * W64.t = {
    
    
    
    (out, offset) <@ __memcpy_u8u8_96_32 (out, offset, in_0);
    return (out, offset);
  }
  
  proc _memcpy_u8u8_128_32 (out:W8.t Array128.t, offset:W64.t,
                            in_0:W8.t Array32.t) : W8.t Array128.t * W64.t = {
    
    
    
    (out, offset) <@ __memcpy_u8u8_128_32 (out, offset, in_0);
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
  
  proc _memcpy_u8u8p_32 (out:W8.t Array32.t, offset:W64.t, in_0:W64.t,
                         inlen:W64.t) : W8.t Array32.t * W64.t = {
    
    
    
    (out, offset) <@ __memcpy_u8u8p_32 (out, offset, in_0, inlen);
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
    var t:W64.t;
    var buf:W8.t Array4.t;
    buf <- witness;
    i <- 0;
    while (i < 8) {
      t <- (zeroextu64 addr.[i]);
      buf <- (Array4.init (fun i_0 => addr_as_bytes.[(4 * i) + i_0]));
      buf <@ __ull_to_bytes_4 (buf, t);
      addr_as_bytes <- Array32.init
                       (fun i_0 => if (4 * i) <= i_0 < (4 * i) + 4
                       then buf.[i_0-(4 * i)] else addr_as_bytes.[i_0]);
      i <- i + 1;
    }
    return (addr_as_bytes);
  }
  
  proc __prf (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    var buf:W8.t Array96.t;
    var padding_buf:W8.t Array32.t;
    var buf_p:W8.t Array96.t;
    var offset:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    buf <- witness;
    buf_p <- witness;
    padding_buf <- witness;
    padding_buf <- (Array32.init (fun i => buf.[0 + i]));
    padding_buf <@ __ull_to_bytes_32 (padding_buf, (W64.of_int 3));
    buf <- Array96.init
           (fun i => if 0 <= i < 0 + 32 then padding_buf.[i-0] else buf.[i]);
    buf_p <- buf;
    offset <- (W64.of_int 32);
    (buf_p,  _0) <@ _x_memcpy_u8u8_96_32 (buf_p, offset, key);
    offset <- (W64.of_int (32 + 32));
    (buf_p,  _1) <@ _x_memcpy_u8u8_96_32 (buf_p, offset, in_0);
    out <@ __core_hash_96 (out, buf_p);
    return (out);
  }
  
  proc _prf (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    
    
    out <@ __prf (out, in_0, key);
    return (out);
  }
  
  proc __prf_ (out:W8.t Array32.t, in_0:W8.t Array32.t, key:W8.t Array32.t) : 
  W8.t Array32.t = {
    
    
    
    out <- out;
    in_0 <- in_0;
    key <- key;
    out <@ _prf (out, in_0, key);
    out <- out;
    return (out);
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
    out <@ __core_hash_128 (out, buf);
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
    (* Erased call to spill *)
    aux <@ __prf_ ((Array32.init (fun i_0 => buf.[32 + i_0])), addr_as_bytes,
    pub_seed);
    buf <- Array96.init
           (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
           else buf.[i_0]);
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
    (* Erased call to spill *)
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
      (* Erased call to spill *)
      aux <@ __addr_to_bytes ((Array32.init (fun i_0 => buf.[32 + i_0])),
      addr);
      buf <- Array64.init
             (fun i_0 => if 32 <= i_0 < 32 + 32 then aux.[i_0-32]
             else buf.[i_0]);
      (* Erased call to unspill *)
      aux <@ __prf_keygen_ ((Array32.init (fun i_0 => outseeds.[(i * 32) + i_0])),
      buf, inseed);
      outseeds <- Array2144.init
                  (fun i_0 => if (i * 32) <= i_0 < (i * 32) + 32
                  then aux.[i_0-(i * 32)] else outseeds.[i_0]);
      (* Erased call to spill *)
      (* Erased call to unspill *)
      i <- i + 1;
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
    (* Erased call to spill *)
    i <- start;
    t <- start;
    t <- (t + steps);
    cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    while (cond) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      addr <@ __set_hash_addr (addr, i);
      (* Erased call to unspill *)
      (out, addr) <@ __thash_f (out, pub_seed, addr);
      (* Erased call to spill *)
      (* Erased call to unspill *)
      i <- (i + (W32.of_int 1));
      cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    }
    (* Erased call to unspill *)
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
    (* Erased call to spill *)
    i <- start;
    t <- start;
    t <- (t + steps);
    cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    while (cond) {
      (* Erased call to spill *)
      (* Erased call to unspill *)
      addr <@ __set_hash_addr (addr, i);
      (* Erased call to unspill *)
      (out, addr) <@ __thash_f_ (out, pub_seed, addr);
      (* Erased call to spill *)
      (* Erased call to unspill *)
      i <- (i + (W32.of_int 1));
      cond <@ __cond_u32_a_below_b_and_a_below_c (i, t, (W32.of_int 16));
    }
    (* Erased call to unspill *)
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
      } else {
        
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
      } else {
        
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
    (* Erased call to spill *)
    (pk, addr) <@ __expand_seed_ (pk, seed, pub_seed, addr);
    (* Erased call to spill *)
    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
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
      (* Erased call to spill *)
      i <- i + 1;
    }
    (* Erased call to unspill *)
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
    (* Erased call to spill *)
    lengths <@ __chain_lengths_ (lengths, msg);
    (sig, addr) <@ __expand_seed_ (sig, seed, pub_seed, addr);
    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
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
    (* Erased call to spill *)
    lengths <@ __chain_lengths_ (lengths, msg);
    i <- 0;
    while (i < 67) {
      chain <- (W32.of_int i);
      addr <@ __set_chain_addr (addr, chain);
      (* Erased call to unspill *)
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
}.

