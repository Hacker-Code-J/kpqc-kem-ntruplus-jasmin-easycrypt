require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import Array768 WArray1536.

module M = {
  proc __mul_i16 (a:W16.t, b:W16.t) : W32.t = {
    var c:W32.t;
    var ad:W32.t;
    var bd:W32.t;
    ad <- (sigextu32 a);
    bd <- (sigextu32 b);
    c <- (ad * bd);
    return c;
  }
  proc __montgomery_reduce (a:W32.t) : W16.t = {
    var t:W16.t;
    var q:W32.t;
    var td:W32.t;
    var r:W32.t;
    q <- (W32.of_int 3457);
    td <- a;
    td <- (td * (W32.of_int 12929));
    t <- (truncateu16 td);
    td <- (sigextu32 t);
    r <- a;
    td <- (td * q);
    r <- (r - td);
    r <- (r `|>>` (W8.of_int 16));
    t <- (truncateu16 r);
    return t;
  }
  proc __barrett_reduce (a:W16.t) : W16.t = {
    var t:W16.t;
    var v:W32.t;
    var td:W32.t;
    var q:W32.t;
    v <- (W32.of_int 19412);
    td <- (sigextu32 a);
    td <- (td * v);
    td <- (td + (W32.of_int 33554432));
    td <- (td `|>>` (W8.of_int 26));
    t <- (truncateu16 td);
    q <- (W32.of_int 3457);
    td <- (sigextu32 t);
    td <- (td * q);
    t <- (truncateu16 td);
    t <- (a - t);
    return t;
  }
  proc __radix2_4_block (rp:W16.t Array768.t, base:W64.t, zeta_0:W16.t) : 
  W16.t Array768.t = {
    var aux:W16.t;
    var i:W64.t;
    var stop:W64.t;
    var low:W16.t;
    var high:W16.t;
    var acc:W32.t;
    var t:W16.t;
    var wd:W32.t;
    var td:W32.t;
    var diff:W16.t;
    var sum:W16.t;
    i <- base;
    stop <- base;
    stop <- (stop + (W64.of_int 4));
    while ((i \ult stop)) {
      low <- rp.[(W64.to_uint i)];
      high <- rp.[(W64.to_uint (i + (W64.of_int 4)))];
      acc <@ __mul_i16 (zeta_0, high);
      t <@ __montgomery_reduce (acc);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd - td);
      diff <- (truncateu16 wd);
      wd <- (sigextu32 low);
      td <- (sigextu32 t);
      wd <- (wd + td);
      sum <- (truncateu16 wd);
      aux <@ __barrett_reduce (diff);
      rp.[(W64.to_uint (i + (W64.of_int 4)))] <- aux;
      aux <@ __barrett_reduce (sum);
      rp.[(W64.to_uint i)] <- aux;
      i <- (i + (W64.of_int 1));
    }
    return rp;
  }
  proc jade_ntruplus_ntruplus768_amd64_ref_ntt_radix2_4 (rp:W16.t Array768.t) : 
  W16.t Array768.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    rp <@ __radix2_4_block (rp, (W64.of_int 0), (W16.of_int 223));
    rp <@ __radix2_4_block (rp, (W64.of_int 8), (W16.of_int 1138));
    rp <@ __radix2_4_block (rp, (W64.of_int 16), (W16.of_int (- 1059)));
    rp <@ __radix2_4_block (rp, (W64.of_int 24), (W16.of_int (- 397)));
    rp <@ __radix2_4_block (rp, (W64.of_int 32), (W16.of_int (- 183)));
    rp <@ __radix2_4_block (rp, (W64.of_int 40), (W16.of_int 1655));
    rp <@ __radix2_4_block (rp, (W64.of_int 48), (W16.of_int 559));
    rp <@ __radix2_4_block (rp, (W64.of_int 56), (W16.of_int (- 1674)));
    rp <@ __radix2_4_block (rp, (W64.of_int 64), (W16.of_int 277));
    rp <@ __radix2_4_block (rp, (W64.of_int 72), (W16.of_int 933));
    rp <@ __radix2_4_block (rp, (W64.of_int 80), (W16.of_int 1723));
    rp <@ __radix2_4_block (rp, (W64.of_int 88), (W16.of_int 437));
    rp <@ __radix2_4_block (rp, (W64.of_int 96), (W16.of_int (- 1514)));
    rp <@ __radix2_4_block (rp, (W64.of_int 104), (W16.of_int 242));
    rp <@ __radix2_4_block (rp, (W64.of_int 112), (W16.of_int 1640));
    rp <@ __radix2_4_block (rp, (W64.of_int 120), (W16.of_int 432));
    rp <@ __radix2_4_block (rp, (W64.of_int 128), (W16.of_int (- 1583)));
    rp <@ __radix2_4_block (rp, (W64.of_int 136), (W16.of_int 696));
    rp <@ __radix2_4_block (rp, (W64.of_int 144), (W16.of_int 774));
    rp <@ __radix2_4_block (rp, (W64.of_int 152), (W16.of_int 1671));
    rp <@ __radix2_4_block (rp, (W64.of_int 160), (W16.of_int 927));
    rp <@ __radix2_4_block (rp, (W64.of_int 168), (W16.of_int 514));
    rp <@ __radix2_4_block (rp, (W64.of_int 176), (W16.of_int 512));
    rp <@ __radix2_4_block (rp, (W64.of_int 184), (W16.of_int 489));
    rp <@ __radix2_4_block (rp, (W64.of_int 192), (W16.of_int 297));
    rp <@ __radix2_4_block (rp, (W64.of_int 200), (W16.of_int 601));
    rp <@ __radix2_4_block (rp, (W64.of_int 208), (W16.of_int 1473));
    rp <@ __radix2_4_block (rp, (W64.of_int 216), (W16.of_int 1130));
    rp <@ __radix2_4_block (rp, (W64.of_int 224), (W16.of_int 1322));
    rp <@ __radix2_4_block (rp, (W64.of_int 232), (W16.of_int 871));
    rp <@ __radix2_4_block (rp, (W64.of_int 240), (W16.of_int 760));
    rp <@ __radix2_4_block (rp, (W64.of_int 248), (W16.of_int 1212));
    rp <@ __radix2_4_block (rp, (W64.of_int 256), (W16.of_int (- 312)));
    rp <@ __radix2_4_block (rp, (W64.of_int 264), (W16.of_int (- 352)));
    rp <@ __radix2_4_block (rp, (W64.of_int 272), (W16.of_int 443));
    rp <@ __radix2_4_block (rp, (W64.of_int 280), (W16.of_int 943));
    rp <@ __radix2_4_block (rp, (W64.of_int 288), (W16.of_int 8));
    rp <@ __radix2_4_block (rp, (W64.of_int 296), (W16.of_int 1250));
    rp <@ __radix2_4_block (rp, (W64.of_int 304), (W16.of_int (- 100)));
    rp <@ __radix2_4_block (rp, (W64.of_int 312), (W16.of_int 1660));
    rp <@ __radix2_4_block (rp, (W64.of_int 320), (W16.of_int (- 31)));
    rp <@ __radix2_4_block (rp, (W64.of_int 328), (W16.of_int 1206));
    rp <@ __radix2_4_block (rp, (W64.of_int 336), (W16.of_int (- 1341)));
    rp <@ __radix2_4_block (rp, (W64.of_int 344), (W16.of_int (- 1247)));
    rp <@ __radix2_4_block (rp, (W64.of_int 352), (W16.of_int 444));
    rp <@ __radix2_4_block (rp, (W64.of_int 360), (W16.of_int 235));
    rp <@ __radix2_4_block (rp, (W64.of_int 368), (W16.of_int 1364));
    rp <@ __radix2_4_block (rp, (W64.of_int 376), (W16.of_int (- 1209)));
    rp <@ __radix2_4_block (rp, (W64.of_int 384), (W16.of_int 361));
    rp <@ __radix2_4_block (rp, (W64.of_int 392), (W16.of_int 230));
    rp <@ __radix2_4_block (rp, (W64.of_int 400), (W16.of_int 673));
    rp <@ __radix2_4_block (rp, (W64.of_int 408), (W16.of_int 582));
    rp <@ __radix2_4_block (rp, (W64.of_int 416), (W16.of_int 1409));
    rp <@ __radix2_4_block (rp, (W64.of_int 424), (W16.of_int 1501));
    rp <@ __radix2_4_block (rp, (W64.of_int 432), (W16.of_int 1401));
    rp <@ __radix2_4_block (rp, (W64.of_int 440), (W16.of_int 251));
    rp <@ __radix2_4_block (rp, (W64.of_int 448), (W16.of_int 1022));
    rp <@ __radix2_4_block (rp, (W64.of_int 456), (W16.of_int (- 1063)));
    rp <@ __radix2_4_block (rp, (W64.of_int 464), (W16.of_int 1053));
    rp <@ __radix2_4_block (rp, (W64.of_int 472), (W16.of_int 1188));
    rp <@ __radix2_4_block (rp, (W64.of_int 480), (W16.of_int 417));
    rp <@ __radix2_4_block (rp, (W64.of_int 488), (W16.of_int (- 1391)));
    rp <@ __radix2_4_block (rp, (W64.of_int 496), (W16.of_int (- 27)));
    rp <@ __radix2_4_block (rp, (W64.of_int 504), (W16.of_int (- 1626)));
    rp <@ __radix2_4_block (rp, (W64.of_int 512), (W16.of_int 1685));
    rp <@ __radix2_4_block (rp, (W64.of_int 520), (W16.of_int (- 315)));
    rp <@ __radix2_4_block (rp, (W64.of_int 528), (W16.of_int 1408));
    rp <@ __radix2_4_block (rp, (W64.of_int 536), (W16.of_int (- 1248)));
    rp <@ __radix2_4_block (rp, (W64.of_int 544), (W16.of_int 400));
    rp <@ __radix2_4_block (rp, (W64.of_int 552), (W16.of_int 274));
    rp <@ __radix2_4_block (rp, (W64.of_int 560), (W16.of_int (- 1543)));
    rp <@ __radix2_4_block (rp, (W64.of_int 568), (W16.of_int 32));
    rp <@ __radix2_4_block (rp, (W64.of_int 576), (W16.of_int (- 1550)));
    rp <@ __radix2_4_block (rp, (W64.of_int 584), (W16.of_int 1531));
    rp <@ __radix2_4_block (rp, (W64.of_int 592), (W16.of_int (- 1367)));
    rp <@ __radix2_4_block (rp, (W64.of_int 600), (W16.of_int (- 124)));
    rp <@ __radix2_4_block (rp, (W64.of_int 608), (W16.of_int 1458));
    rp <@ __radix2_4_block (rp, (W64.of_int 616), (W16.of_int 1379));
    rp <@ __radix2_4_block (rp, (W64.of_int 624), (W16.of_int (- 940)));
    rp <@ __radix2_4_block (rp, (W64.of_int 632), (W16.of_int (- 1681)));
    rp <@ __radix2_4_block (rp, (W64.of_int 640), (W16.of_int 22));
    rp <@ __radix2_4_block (rp, (W64.of_int 648), (W16.of_int 1709));
    rp <@ __radix2_4_block (rp, (W64.of_int 656), (W16.of_int (- 275)));
    rp <@ __radix2_4_block (rp, (W64.of_int 664), (W16.of_int 1108));
    rp <@ __radix2_4_block (rp, (W64.of_int 672), (W16.of_int 354));
    rp <@ __radix2_4_block (rp, (W64.of_int 680), (W16.of_int (- 1728)));
    rp <@ __radix2_4_block (rp, (W64.of_int 688), (W16.of_int (- 968)));
    rp <@ __radix2_4_block (rp, (W64.of_int 696), (W16.of_int 858));
    rp <@ __radix2_4_block (rp, (W64.of_int 704), (W16.of_int 1221));
    rp <@ __radix2_4_block (rp, (W64.of_int 712), (W16.of_int (- 218)));
    rp <@ __radix2_4_block (rp, (W64.of_int 720), (W16.of_int 294));
    rp <@ __radix2_4_block (rp, (W64.of_int 728), (W16.of_int (- 732)));
    rp <@ __radix2_4_block (rp, (W64.of_int 736), (W16.of_int (- 1095)));
    rp <@ __radix2_4_block (rp, (W64.of_int 744), (W16.of_int 892));
    rp <@ __radix2_4_block (rp, (W64.of_int 752), (W16.of_int 1588));
    rp <@ __radix2_4_block (rp, (W64.of_int 760), (W16.of_int (- 779)));
    return rp;
  }
}.
