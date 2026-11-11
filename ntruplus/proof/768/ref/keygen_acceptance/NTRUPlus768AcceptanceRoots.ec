require import AllCore IntDiv List Ring StdOrder BitEncoding.
from Jasmin require import JUtils.
require import NTRUPlus768BasemulAlgebra NTRUPlus768NTTSchedule.
require import NTRUPlus768PolyBasemulAlgebra NTRUPlus768PolyBasemulProof.
import IntOrder.

(* Paired square roots in the exact terminal-block order.  The following
   finite checks validate both the source NTT constants and Euler values. *)
op [opaque] acceptance_roots : int list = [
  1003; 2454; 1439; 2018; 438; 3019; 1026; 2431; 203; 3254; 1470; 1987;
  809; 2648; 1090; 2367; 1374; 2083; 1375; 2082; 110; 3347; 1631; 1826;
  833; 2624; 1383; 2074; 1687; 1770; 1726; 1731; 589; 2868; 1285; 2172;
  1280; 2177; 506; 2951; 1522; 1935; 1008; 2449; 1717; 1740; 1228; 2229;
  152; 3305; 449; 3008; 1557; 1900; 427; 3030; 1503; 1954; 632; 2825;
  226; 3231; 986; 2471; 1271; 2186; 1048; 2409; 331; 3126; 728; 2729;
  919; 2538; 736; 2721; 612; 2845; 1171; 2286; 328; 3129; 605; 2852;
  643; 2814; 1080; 2377; 878; 2579; 636; 2821; 604; 2853; 1036; 2421;
  674; 2783; 126; 3331; 1511; 1946; 1575; 1882; 160; 3297; 801; 2656;
  1457; 2000; 1370; 2087; 620; 2837; 79; 3378; 836; 2621; 741; 2716;
  1491; 1966; 1243; 2214; 376; 3081; 19; 3438; 547; 2910; 92; 3365;
  1652; 1805; 1150; 2307; 1255; 2202; 91; 3366; 131; 3326; 591; 2866;
  974; 2483; 1649; 1808; 1653; 1804; 1599; 1858; 1216; 2241; 135; 3322;
  1372; 2085; 41; 3416; 20; 3437; 332; 3125; 250; 3207; 693; 2764;
  621; 2836; 629; 2828; 880; 2577; 780; 2677; 1110; 2347; 1141; 2316;
  47; 3410; 1294; 2163; 1624; 1833; 1389; 2068; 442; 3015; 1651; 1806;
  1472; 1985; 1619; 1838; 1115; 2342; 1224; 2233; 1456; 2001; 662; 2795;
  915; 2542; 1361; 2096; 1272; 2185; 1701; 1756; 1385; 2072; 1208; 2249;
  1297; 2160; 1286; 2171; 656; 2801; 1210; 2247; 1602; 1855; 320; 3137;
  717; 2740; 543; 2914; 307; 3150; 435; 3022; 1348; 2109; 252; 3205;
  971; 2486; 475; 2982; 38; 3419; 752; 2705; 1482; 1975; 1672; 1785;
  1240; 2217; 158; 3299; 182; 3275; 947; 2510; 1182; 2275; 262; 3195;
  1157; 2300; 153; 3304; 1094; 2363; 184; 3273; 270; 3187; 1025; 2432;
  82; 3375; 713; 2744; 259; 3198; 151; 3306; 1509; 1948; 159; 3298;
  1258; 2199; 1242; 2215; 1560; 1897; 1697; 1760; 1386; 2071; 500; 2957;
  40; 3417; 664; 2793; 679; 2778; 209; 3248; 155; 3302; 884; 2573;
  869; 2588; 94; 3363; 1237; 2220; 1175; 2282; 1441; 2016; 413; 3044;
  1001; 2456; 23; 3434; 1012; 2445; 897; 2560; 1178; 2279; 887; 2570;
  1264; 2193; 451; 3006; 1485; 1972; 452; 3005; 854; 2603; 343; 3114;
  304; 3153; 898; 2559; 691; 2766; 1666; 1791; 5; 3452; 83; 3374;
  195; 3262; 220; 3237; 709; 2748; 707; 2750; 1405; 2052; 876; 2581;
  1451; 2006; 579; 2878; 1277; 2180; 1618; 1839; 406; 3051; 517; 2940
].
op [opaque] acceptance_sqrts : int list = [
  1003; 1439; 438; 1026; 203; 1470; 809; 1090; 1374; 1375; 110; 1631;
  833; 1383; 1687; 1726; 589; 1285; 1280; 506; 1522; 1008; 1717; 1228;
  152; 449; 1557; 427; 1503; 632; 226; 986; 1271; 1048; 331; 728;
  919; 736; 612; 1171; 328; 605; 643; 1080; 878; 636; 604; 1036;
  674; 126; 1511; 1575; 160; 801; 1457; 1370; 620; 79; 836; 741;
  1491; 1243; 376; 19; 547; 92; 1652; 1150; 1255; 91; 131; 591;
  974; 1649; 1653; 1599; 1216; 135; 1372; 41; 20; 332; 250; 693;
  621; 629; 880; 780; 1110; 1141; 47; 1294; 1624; 1389; 442; 1651;
  1472; 1619; 1115; 1224; 1456; 662; 915; 1361; 1272; 1701; 1385; 1208;
  1297; 1286; 656; 1210; 1602; 320; 717; 543; 307; 435; 1348; 252;
  971; 475; 38; 752; 1482; 1672; 1240; 158; 182; 947; 1182; 262;
  1157; 153; 1094; 184; 270; 1025; 82; 713; 259; 151; 1509; 159;
  1258; 1242; 1560; 1697; 1386; 500; 40; 664; 679; 209; 155; 884;
  869; 94; 1237; 1175; 1441; 413; 1001; 23; 1012; 897; 1178; 887;
  1264; 451; 1485; 452; 854; 343; 304; 898; 691; 1666; 5; 83;
  195; 220; 709; 707; 1405; 876; 1451; 579; 1277; 1618; 406; 517
].
op [opaque] acceptance_root (j:int) : int = nth 0 acceptance_roots j.
op acceptance_square_mod (x:int) = (x*x) %% 3457.
op acceptance_mul_mod (x y:int) = (x*y) %% 3457.
op acceptance_pow2 (x:int) = acceptance_square_mod (x %% 3457).
op acceptance_pow4 (x:int) = acceptance_square_mod (acceptance_pow2 x).
op acceptance_pow8 (x:int) = acceptance_square_mod (acceptance_pow4 x).
op acceptance_pow16 (x:int) = acceptance_square_mod (acceptance_pow8 x).
op acceptance_pow32 (x:int) = acceptance_square_mod (acceptance_pow16 x).
op acceptance_pow64 (x:int) = acceptance_square_mod (acceptance_pow32 x).
op acceptance_pow128 (x:int) = acceptance_square_mod (acceptance_pow64 x).
op acceptance_pow256 (x:int) = acceptance_square_mod (acceptance_pow128 x).
op acceptance_pow512 (x:int) = acceptance_square_mod (acceptance_pow256 x).
op acceptance_pow1024 (x:int) = acceptance_square_mod (acceptance_pow512 x).
op acceptance_euler_mod (x:int) =
  let p2=acceptance_square_mod (x %%3457) in
  let p4=acceptance_square_mod p2 in
  let p8=acceptance_square_mod p4 in
  let p16=acceptance_square_mod p8 in
  let p32=acceptance_square_mod p16 in
  let p64=acceptance_square_mod p32 in
  let p128=acceptance_square_mod p64 in
  let p256=acceptance_square_mod p128 in
  let p512=acceptance_square_mod p256 in
  let p1024=acceptance_square_mod p512 in
  acceptance_mul_mod (acceptance_mul_mod p1024 p512) (acceptance_mul_mod p128 p64).

lemma acceptance_square_mod_power x n : 0<=n =>
 acceptance_square_mod (x^n %% 3457) = x^(n+n) %%3457.
proof.
 move=> hn; rewrite /acceptance_square_mod modzMm exprD_nneg 1:hn 1:hn //.
qed.
lemma acceptance_mul_mod_power x n m : 0<=n => 0<=m =>
 acceptance_mul_mod (x^n %%3457) (x^m %%3457) = x^(n+m) %%3457.
proof.
 move=> hn hm; rewrite /acceptance_mul_mod modzMm exprD_nneg 1:hn 1:hm //.
qed.
lemma acceptance_pow2E x : acceptance_pow2 x = x^2 %%3457.
proof.
 rewrite /acceptance_pow2 -{1}(expr1 x).
 by rewrite acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow4E x : acceptance_pow4 x = x^4 %%3457.
proof.
 by rewrite /acceptance_pow4 acceptance_pow2E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow8E x : acceptance_pow8 x = x^8 %%3457.
proof.
 by rewrite /acceptance_pow8 acceptance_pow4E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow16E x : acceptance_pow16 x = x^16 %%3457.
proof.
 by rewrite /acceptance_pow16 acceptance_pow8E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow32E x : acceptance_pow32 x = x^32 %%3457.
proof.
 by rewrite /acceptance_pow32 acceptance_pow16E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow64E x : acceptance_pow64 x = x^64 %%3457.
proof.
 by rewrite /acceptance_pow64 acceptance_pow32E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow128E x : acceptance_pow128 x = x^128 %%3457.
proof.
 by rewrite /acceptance_pow128 acceptance_pow64E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow256E x : acceptance_pow256 x = x^256 %%3457.
proof.
 by rewrite /acceptance_pow256 acceptance_pow128E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow512E x : acceptance_pow512 x = x^512 %%3457.
proof.
 by rewrite /acceptance_pow512 acceptance_pow256E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_pow1024E x : acceptance_pow1024 x = x^1024 %%3457.
proof.
 by rewrite /acceptance_pow1024 acceptance_pow512E acceptance_square_mod_power 1:// /=.
qed.
lemma acceptance_euler_modE x : acceptance_euler_mod x = x^1728 %%3457.
proof.
 change (acceptance_mul_mod
   (acceptance_mul_mod (acceptance_pow1024 x) (acceptance_pow512 x))
   (acceptance_mul_mod (acceptance_pow128 x) (acceptance_pow64 x)) = x^1728 %%3457).
 rewrite acceptance_pow1024E acceptance_pow512E
   acceptance_pow128E acceptance_pow64E.
 rewrite (acceptance_mul_mod_power x 1024 512) 1,2://.
 rewrite (acceptance_mul_mod_power x 128 64) 1,2://.
 by rewrite acceptance_mul_mod_power 1,2:// /=.
qed.

lemma acceptance_roots_size : size acceptance_roots = 384.
proof. by rewrite /acceptance_roots /=. qed.
lemma acceptance_roots_range_certificate : all (fun r=>0<r<3457) acceptance_roots.
proof. by rewrite /acceptance_roots /=. qed.
lemma acceptance_sqrts_size : size acceptance_sqrts=192.
proof. by rewrite /acceptance_sqrts /=. qed.
lemma acceptance_roots_pair_certificate :
 acceptance_roots=flatten(map(fun r=>[r;(-r) %%3457]) acceptance_sqrts).
proof. by rewrite /acceptance_roots /acceptance_sqrts /=. qed.
op [opaque] acceptance_terminal_values : int list =
 flatten(map(fun c=>[(c*2775) %%3457;((-c)*2775) %%3457]) (drop 96 zetas192_coeffs)).
lemma acceptance_roots_square_certificate :
 map(fun r=>r^2 %%3457) acceptance_sqrts = acceptance_terminal_values.
proof.
 by rewrite /acceptance_sqrts /acceptance_terminal_values /zetas192_coeffs /=.
qed.
lemma acceptance_terminal_values_nth k : 0<=k<192 =>
 nth 0 acceptance_terminal_values k=terminal_value k.
proof.
 move=> hk.
 have hhalf:0<=k %/2<96 by smt().
 have hs:0<=k %/2<size(drop 96 zetas192_coeffs).
 + by rewrite size_drop /=.
 rewrite /acceptance_terminal_values (BitEncoding.BitChunking.nth_flatten 0 2).
 + by rewrite allP=>ys /mapP[r [_ ->]] /=.
 rewrite (nth_map 0) 1:hs nth_drop 1:// 1:/#.
 have hi:0<=96+k %/2<size zetas192_coeffs by rewrite size_zetas192_coeffs; smt().
 rewrite (nth_change_dfl witness 0 zetas192_coeffs (96+k %/2) hi).
 rewrite -(block_zeta_math_terminal_value k hk) /block_zeta_math /zeta_decode /block_zeta.
 case (k %%2=0)=>he.
 + rewrite he /= (zeta96_coeffE (k %/2) hhalf) /zeta_coeff /zetas192_coeff /Rinv /q.
   done.
 have ho:k %%2=1 by smt(modz_cmp).
 rewrite ho /= (zeta96_neg_coeffE (k %/2) hhalf) /zeta_coeff /zetas192_coeff /Rinv /q.
 done.
qed.
lemma acceptance_sqrt_square k : 0<=k<192 =>
 (nth 0 acceptance_sqrts k)^2 %%3457=terminal_value k.
proof.
 move=> hk.
 rewrite -(acceptance_terminal_values_nth k hk) -acceptance_roots_square_certificate.
 have hs:0<=k<size acceptance_sqrts by rewrite acceptance_sqrts_size.
 by rewrite (nth_map 0) 1:hs.
qed.
lemma acceptance_root_pair_nth k (b:bool) : 0<=k<192 =>
 acceptance_root(2*k+b2i b)=
 (if b then (-nth 0 acceptance_sqrts k) %%3457 else nth 0 acceptance_sqrts k).
proof.
 move=> hk; rewrite /acceptance_root acceptance_roots_pair_certificate.
 rewrite (BitEncoding.BitChunking.nth_flatten 0 2).
 + by rewrite allP=>ys /mapP[r [_ ->]] /=.
 have hdiv:(2*k+b2i b) %/2=k by case b=> /=; smt().
 have hs:0<=k<size acceptance_sqrts by rewrite acceptance_sqrts_size.
 rewrite hdiv (nth_map 0) 1:hs.
 case b=> /=; have he:(2*k+1) %%2=1 by smt().
 + by rewrite he /=.
 + have hz:(2*k) %%2=0 by smt().
   by rewrite hz /=.
qed.
lemma acceptance_roots_euler_certificate :
 all (fun r=>acceptance_euler_mod r=3456) acceptance_roots.
proof.
 by rewrite /acceptance_roots /acceptance_euler_mod /acceptance_mul_mod
   /acceptance_square_mod /=.
qed.

lemma acceptance_root_range j : 0<=j<384 => 0<acceptance_root j<3457.
proof.
 move=> hj; have h:=acceptance_roots_range_certificate.
 rewrite allP in h; apply h.
 rewrite /acceptance_root; apply mem_nth; by rewrite acceptance_roots_size.
qed.
lemma acceptance_root_square k (b:bool) : 0<=k<192 =>
 (acceptance_root(2*k+b2i b)^2) %%3457=terminal_value k.
proof.
 move=> hk; rewrite (acceptance_root_pair_nth k b hk).
 case b=>hb.
 + rewrite (modz_expr (-nth 0 acceptance_sqrts k) 2 3457) 1://.
   have hn:(-nth 0 acceptance_sqrts k)^2=(nth 0 acceptance_sqrts k)^2 by ring.
   by rewrite hn (acceptance_sqrt_square k hk).
 + exact (acceptance_sqrt_square k hk).
qed.
lemma acceptance_root_neg k : 0<=k<192 =>
 acceptance_root(2*k+1)=(-acceptance_root(2*k)) %%3457.
proof.
 move=> hk.
 have h0:=acceptance_root_pair_nth k false hk.
 have h1:=acceptance_root_pair_nth k true hk.
 by move:h0 h1=> /= -> ->.
qed.
lemma acceptance_root_euler j : 0<=j<384 =>
 acceptance_root j ^1728 %%3457=3456.
proof.
 move=> hj; rewrite -acceptance_euler_modE.
 have h:=acceptance_roots_euler_certificate; rewrite allP in h; apply h.
 rewrite /acceptance_root; apply mem_nth; by rewrite acceptance_roots_size.
qed.

lemma acceptance_square_root_polynomial r z :
 r^2 %%3457=z => (z^192-z^96+1) %%3457=0 =>
 (r^384-r^192+1) %%3457=0.
proof.
 move=> hz hp.
 have h96:r^192 %%3457=z^96 %%3457.
 + rewrite (_:192=2*96) 1:// exprM.
   by rewrite -(modz_expr (r^2) 96 3457) 1:// hz.
 have h192:r^384 %%3457=z^192 %%3457.
 + rewrite (_:384=2*192) 1:// exprM.
   by rewrite -(modz_expr (r^2) 192 3457) 1:// hz.
 by rewrite -modzDml -modzBm h192 h96 modzBm modzDml.
qed.
lemma acceptance_root_polynomial j : 0<=j<384 =>
 (acceptance_root j ^384-acceptance_root j ^192+1) %%3457=0.
proof.
 move=> hj.
 have hk:0<=j %/2<192 by smt().
 have hb:b2i(j %%2=1)=j %%2 by rewrite /b2i; smt(modz_cmp).
 have hjj:j=2*(j %/2)+b2i(j %%2=1) by rewrite hb; smt(divz_eq).
 have hs:=acceptance_root_square (j %/2) (j %%2=1) hk.
 rewrite -hjj in hs.
 apply (acceptance_square_root_polynomial (acceptance_root j) (terminal_value(j %/2)) hs).
 by have ht:=terminal_value_root (j %/2) hk; move:ht; rewrite /q.
qed.
