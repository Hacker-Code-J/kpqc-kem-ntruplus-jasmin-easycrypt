require import AllCore BitEncoding IntDiv List Ring StdOrder.
from Jasmin require import JWord.

require import NTRUPlus768BasemulAlgebra.

import IntOrder.

op n : int = 768.
op d : int = 4.
op nd : int = n %/ d.
op zeta_root : int = 22.

op zetas192_coeffs : int list = [
  (-147); -1033; -682; -248; -708; 682; 1; -722;
  -723; -257; -1124; -867; -256; 1484; 1262; -1590;
  1611; 222; 1164; -1346; 1716; -1521; -357; 395;
  -455; 639; 502; 655; -699; 541; 95; -1577;
  -1241; 550; -44; 39; -820; -216; -121; -757;
  -348; 937; 893; 387; -603; 1713; -1105; 1058;
  1449; 837; 901; 1637; -569; -1617; -1530; 1199;
  50; -830; -625; 4; 176; -156; 1257; -1507;
  -380; -606; 1293; 661; 1428; -1580; -565; -992;
  548; -800; 64; -371; 961; 641; 87; 630;
  675; -834; 205; 54; -1081; 1351; 1413; -1331;
  -1673; -1267; -1558; 281; -1464; -588; 1015; 436;
  223; 1138; -1059; -397; -183; 1655; 559; -1674;
  277; 933; 1723; 437; -1514; 242; 1640; 432;
  -1583; 696; 774; 1671; 927; 514; 512; 489;
  297; 601; 1473; 1130; 1322; 871; 760; 1212;
  -312; -352; 443; 943; 8; 1250; -100; 1660;
  -31; 1206; -1341; -1247; 444; 235; 1364; -1209;
  361; 230; 673; 582; 1409; 1501; 1401; 251;
  1022; -1063; 1053; 1188; 417; -1391; -27; -1626;
  1685; -315; 1408; -1248; 400; 274; -1543; 32;
  -1550; 1531; -1367; -124; 1458; 1379; -940; -1681;
  22; 1709; -275; 1108; 354; -1728; -968; 858;
  1221; -218; 294; -732; -1095; 892; 1588; -779
].

op zetas192_exponents : int list = [
  0; 96; 32; 64; 160; 320; 16; 112;
  208; 80; 176; 272; 8; 152; 56; 200;
  104; 248; 40; 184; 88; 232; 136; 280;
  4; 148; 76; 220; 28; 172; 100; 244;
  52; 196; 124; 268; 20; 164; 92; 236;
  44; 188; 116; 260; 68; 212; 140; 284;
  2; 146; 74; 218; 38; 182; 110; 254;
  14; 158; 86; 230; 50; 194; 122; 266;
  26; 170; 98; 242; 62; 206; 134; 278;
  10; 154; 82; 226; 46; 190; 118; 262;
  22; 166; 94; 238; 58; 202; 130; 274;
  34; 178; 106; 250; 70; 214; 142; 286;
  1; 145; 73; 217; 37; 181; 109; 253;
  19; 163; 91; 235; 55; 199; 127; 271;
  7; 151; 79; 223; 43; 187; 115; 259;
  25; 169; 97; 241; 61; 205; 133; 277;
  13; 157; 85; 229; 49; 193; 121; 265;
  31; 175; 103; 247; 67; 211; 139; 283;
  5; 149; 77; 221; 41; 185; 113; 257;
  23; 167; 95; 239; 59; 203; 131; 275;
  11; 155; 83; 227; 47; 191; 119; 263;
  29; 173; 101; 245; 65; 209; 137; 281;
  17; 161; 89; 233; 53; 197; 125; 269;
  35; 179; 107; 251; 71; 215; 143; 287
].

op terminal_exponents96 : int list = drop 96 zetas192_exponents.

op figure22_indices192 : int list = [
  1; 289; 145; 433; 73; 361; 217; 505;
  37; 325; 181; 469; 109; 397; 253; 541;
  19; 307; 163; 451; 91; 379; 235; 523;
  55; 343; 199; 487; 127; 415; 271; 559;
  7; 295; 151; 439; 79; 367; 223; 511;
  43; 331; 187; 475; 115; 403; 259; 547;
  25; 313; 169; 457; 97; 385; 241; 529;
  61; 349; 205; 493; 133; 421; 277; 565;
  13; 301; 157; 445; 85; 373; 229; 517;
  49; 337; 193; 481; 121; 409; 265; 553;
  31; 319; 175; 463; 103; 391; 247; 535;
  67; 355; 211; 499; 139; 427; 283; 571;
  5; 293; 149; 437; 77; 365; 221; 509;
  41; 329; 185; 473; 113; 401; 257; 545;
  23; 311; 167; 455; 95; 383; 239; 527;
  59; 347; 203; 491; 131; 419; 275; 563;
  11; 299; 155; 443; 83; 371; 227; 515;
  47; 335; 191; 479; 119; 407; 263; 551;
  29; 317; 173; 461; 101; 389; 245; 533;
  65; 353; 209; 497; 137; 425; 281; 569;
  17; 305; 161; 449; 89; 377; 233; 521;
  53; 341; 197; 485; 125; 413; 269; 557;
  35; 323; 179; 467; 107; 395; 251; 539;
  71; 359; 215; 503; 143; 431; 287; 575
].

op zetas192_coeff (i : int) : int = nth witness zetas192_coeffs i.
op zetas192_exp (i : int) : int = nth witness zetas192_exponents i.
op terminal_exp (i : int) : int = nth witness terminal_exponents96 i.
op figure22_index (i : int) : int = nth witness figure22_indices192 i.

op decode_mont (c : int) : int = (c * Rinv) %% q.
op centered_mont_of (x : int) : int =
  let y = (x * (R %% q)) %% q in
  if y <= q %/ 2 then y else y - q.

op decoded_zetas192_from_coeffs : int list =
  map decode_mont zetas192_coeffs.
op decoded_zetas192_from_exponents : int list =
  map (fun e => (zeta_root ^ e) %% q) zetas192_exponents.

op generated_zetas192_coeffs : int list =
  map (fun e => centered_mont_of ((zeta_root ^ e) %% q)) zetas192_exponents.

op terminal_value (i : int) : int = (zeta_root ^ figure22_index i) %% q.

op ell : int = 576.
op split3_children (p : int) : int list =
  [p %/ 3; (p + ell) %/ 3; (p + 2 * ell) %/ 3].
op split2_children (p : int) : int list =
  [p %/ 2; (p + ell) %/ 2].
op split3_twiddles (p : int) : int list =
  [p %/ 3; (2 * p) %/ 3].
op split2_twiddle (p : int) : int = p %/ 2.

op roots_initial : int list = [ell %/ 6; 5 * ell %/ 6].
op roots_after_radix3 : int list = flatten (map split3_children roots_initial).
op roots_after_radix2_64 : int list = flatten (map split2_children roots_after_radix3).
op roots_after_radix2_32 : int list = flatten (map split2_children roots_after_radix2_64).
op roots_after_radix2_16 : int list = flatten (map split2_children roots_after_radix2_32).
op roots_after_radix2_8 : int list = flatten (map split2_children roots_after_radix2_16).
op roots_after_radix2_4 : int list = flatten (map split2_children roots_after_radix2_8).

op generated_terminal_exponents192 : int list = roots_after_radix2_4.
op generated_terminal_exponents96 : int list = map split2_twiddle roots_after_radix2_8.
op generated_figure22_indices192 : int list = roots_after_radix2_4.

op generated_figure22_rhs192 : int list =
  flatten
    (map (fun e => [e; e + ell %/ 2]) terminal_exponents96).

op generated_ntt_twiddle_exponents : int list =
  [0] ++
  [ell %/ 6] ++
  flatten (map split3_twiddles roots_initial) ++
  map split2_twiddle roots_after_radix3 ++
  map split2_twiddle roots_after_radix2_64 ++
  map split2_twiddle roots_after_radix2_32 ++
  map split2_twiddle roots_after_radix2_16 ++
  map split2_twiddle roots_after_radix2_8.

op ntt_stage1_start : int = 1.
op ntt_stage1_count : int = 1.
op ntt_radix3_start : int = 2.
op ntt_radix3_count : int = 4.
op ntt_radix2_64_start : int = 6.
op ntt_radix2_64_count : int = 6.
op ntt_radix2_32_start : int = 12.
op ntt_radix2_32_count : int = 12.
op ntt_radix2_16_start : int = 24.
op ntt_radix2_16_count : int = 24.
op ntt_radix2_8_start : int = 48.
op ntt_radix2_8_count : int = 48.
op ntt_radix2_4_start : int = 96.
op ntt_radix2_4_count : int = 96.

op invntt_rev_index (j : int) : int = 191 - j.

lemma ndE : nd = 192.
proof. by rewrite /nd /n /d /=. qed.

lemma size_zetas192_coeffs :
  size zetas192_coeffs = 192.
proof. by rewrite /zetas192_coeffs /=. qed.

lemma size_zetas192_exponents :
  size zetas192_exponents = 192.
proof. by rewrite /zetas192_exponents /=. qed.

lemma size_terminal_exponents96 :
  size terminal_exponents96 = 96.
proof.
  by rewrite /terminal_exponents96 size_drop /zetas192_exponents /=.
qed.

lemma size_figure22_indices192 :
  size figure22_indices192 = 192.
proof. by rewrite /figure22_indices192 /=. qed.

lemma generated_terminal_scheduleE :
  generated_terminal_exponents192 = figure22_indices192.
proof.
  rewrite /generated_terminal_exponents192 /generated_figure22_indices192.
  rewrite /roots_after_radix2_4 /roots_after_radix2_8 /roots_after_radix2_16.
  rewrite /roots_after_radix2_32 /roots_after_radix2_64 /roots_after_radix3.
  rewrite /roots_initial /split3_children /split2_children /ell /=.
  done.
qed.

lemma generated_terminal_suffixE :
  generated_terminal_exponents96 = terminal_exponents96.
proof.
  rewrite /generated_terminal_exponents96 /terminal_exponents96.
  rewrite /roots_after_radix2_4 /roots_after_radix2_8 /roots_after_radix2_16.
  rewrite /roots_after_radix2_32 /roots_after_radix2_64 /roots_after_radix3.
  rewrite /roots_initial /split3_children /split2_children /ell /=.
  done.
qed.

lemma generated_twiddle_scheduleE :
  generated_ntt_twiddle_exponents = zetas192_exponents.
proof.
  rewrite /generated_ntt_twiddle_exponents /zetas192_exponents.
  rewrite /roots_after_radix2_4 /roots_after_radix2_8 /roots_after_radix2_16.
  rewrite /roots_after_radix2_32 /roots_after_radix2_64 /roots_after_radix3.
  rewrite /roots_initial /split3_children /split2_children /split3_twiddles.
  rewrite /split2_twiddle /ell /=.
  done.
qed.

lemma decoded_zetas192E :
  decoded_zetas192_from_coeffs = decoded_zetas192_from_exponents.
proof.
  rewrite /decoded_zetas192_from_coeffs /decoded_zetas192_from_exponents.
  rewrite /decode_mont /zetas192_coeffs /zetas192_exponents.
  rewrite /zeta_root /q /Rinv /=.
  done.
qed.

lemma generated_zetas192_coeffsE :
  zetas192_coeffs = generated_zetas192_coeffs.
proof.
  rewrite /generated_zetas192_coeffs /zetas192_coeffs /zetas192_exponents.
  rewrite /centered_mont_of /zeta_root /q /R /=.
  done.
qed.

lemma centered_mont_of_range (x : int) :
  0 <= x < q => -q < centered_mont_of x < q.
proof.
  move=> Hx.
  rewrite /centered_mont_of.
  pose y := (x * (R %% q)) %% q.
  have Hy : 0 <= y < q by rewrite /y; smt().
  case (y <= q %/ 2) => Hle.
  + rewrite /y; smt().
  rewrite /y; smt().
qed.

lemma zeta_order_576 :
  zeta_root ^ 576 %% q = 1.
proof. by rewrite /zeta_root /q /=. qed.

lemma zeta_order_288_neq1 :
  zeta_root ^ 288 %% q <> 1.
proof. by rewrite /zeta_root /q /=. qed.

lemma zeta_order_288_value :
  zeta_root ^ 288 %% q = q - 1.
proof. by rewrite /zeta_root /q /=. qed.

lemma zeta_order_192_neq1 :
  zeta_root ^ 192 %% q <> 1.
proof. by rewrite /zeta_root /q /=. qed.

lemma zeta_exact_order_576 :
  zeta_root ^ 576 %% q = 1 /\ zeta_root ^ 288 %% q <> 1 /\ zeta_root ^ 192 %% q <> 1.
proof. by rewrite zeta_order_576 zeta_order_288_neq1 zeta_order_192_neq1. qed.

lemma modz_expr (x m modulus : int) :
  0 <= m => ((x %% modulus) ^ m) %% modulus = (x ^ m) %% modulus.
proof.
  move=> Hm.
  elim m Hm.
  + rewrite !expr0.
    done.
  move=> k Hk IH.
  rewrite !exprS 1:/#.
  + done.
  rewrite -modzMmr IH modzMml modzMmr.
  done.
qed.

lemma zeta_period_576 (k r : int) :
  0 <= k =>
  0 <= r =>
  zeta_root ^ (k * 576 + r) %% q = zeta_root ^ r %% q.
proof.
  move=> Hk Hr.
  have -> : k * 576 + r = 576 * k + r by smt().
  rewrite exprD_nneg 1:/# 1:Hr exprM.
  rewrite -modzMml.
  have Hpow := modz_expr (zeta_root ^ 576) k q Hk.
  rewrite zeta_order_576 in Hpow.
  rewrite -Hpow expr1z /q /=.
  done.
qed.

lemma zetas192_coeff_range (i : int) :
  0 <= i < 192 => -q < zetas192_coeff i < q.
proof.
  move=> Hi.
  rewrite /zetas192_coeff generated_zetas192_coeffsE /generated_zetas192_coeffs.
  rewrite (nth_map witness).
  + by rewrite size_zetas192_exponents.
  apply centered_mont_of_range.
  rewrite /zetas192_exp.
  smt().
qed.

lemma decoded_zetas192_nthE (i : int) :
  nth witness decoded_zetas192_from_coeffs i =
  nth witness decoded_zetas192_from_exponents i.
proof.
  move/(congr1 (fun xs => nth witness xs i)): decoded_zetas192E.
  done.
qed.

lemma decoded_zetas192_coeff_nthE (i : int) :
  0 <= i < 192 =>
  nth witness decoded_zetas192_from_coeffs i =
  decode_mont (zetas192_coeff i).
proof.
  move=> Hi.
  change (nth witness decoded_zetas192_from_coeffs i =
          decode_mont (nth witness zetas192_coeffs i)).
  rewrite /decoded_zetas192_from_coeffs (nth_map witness).
  + by rewrite size_zetas192_coeffs.
  done.
qed.

lemma decoded_zetas192_exp_nthE (i : int) :
  0 <= i < 192 =>
  nth witness decoded_zetas192_from_exponents i =
  (zeta_root ^ zetas192_exp i) %% q.
proof.
  move=> Hi.
  change (nth witness decoded_zetas192_from_exponents i =
          (zeta_root ^ nth witness zetas192_exponents i) %% q).
  rewrite /decoded_zetas192_from_exponents.
  rewrite (nth_map witness).
  + by rewrite size_zetas192_exponents.
  done.
qed.

lemma zetas192_relation (i : int) :
  0 <= i < 192 =>
  decode_mont (zetas192_coeff i) = (zeta_root ^ zetas192_exp i) %% q.
proof.
  move=> Hi.
  have Hcoeff := decoded_zetas192_coeff_nthE i Hi.
  have Hexp := decoded_zetas192_exp_nthE i Hi.
  rewrite -Hcoeff -Hexp.
  exact (decoded_zetas192_nthE i).
qed.

lemma terminal_exponents_suffix (i : int) :
  0 <= i < 96 => terminal_exp i = zetas192_exp (96 + i).
proof.
  move=> Hi.
  rewrite /terminal_exp /terminal_exponents96 nth_drop 1:// 1:/#.
  by rewrite /zetas192_exp.
qed.

lemma generated_figure22_rhsE :
  generated_figure22_rhs192 = figure22_indices192.
proof.
  rewrite /generated_figure22_rhs192 /terminal_exponents96.
  rewrite /figure22_indices192 /ell /=.
  done.
qed.

lemma nth_generated_figure22_pair (xs : int list) (i : int) :
  0 <= i < 2 * size xs =>
  nth witness
      (flatten (map (fun e => [e; e + ell %/ 2]) xs)) i =
    if i %% 2 = 0 then nth witness xs (i %/ 2)
    else nth witness xs (i %/ 2) + ell %/ 2.
proof.
  move=> Hi.
  rewrite (BitEncoding.BitChunking.nth_flatten witness 2).
  + rewrite allP => ys /mapP [e [_ ->]] /=.
    done.
  have Hhalf : 0 <= i %/ 2 < size xs by smt().
  rewrite (nth_map witness) 1:Hhalf.
  simplify.
  case (i %% 2 = 0) => Hpar.
  + done.
  have Hrem : 0 <= i %% 2 < 2 by smt().
  have Hmod : i %% 2 = 1 by smt().
  rewrite Hmod /=.
  done.
qed.

lemma figure22_index_relation (i : int) :
  0 <= i < 192 =>
  figure22_index i =
    if i %% 2 = 0 then terminal_exp (i %/ 2)
    else terminal_exp (i %/ 2) + 288.
proof.
  move=> Hi.
  change (nth witness figure22_indices192 i =
          if i %% 2 = 0 then nth witness terminal_exponents96 (i %/ 2)
          else nth witness terminal_exponents96 (i %/ 2) + 288).
  rewrite -generated_figure22_rhsE.
  change
    (nth witness
       (flatten (map (fun e => [e; e + ell %/ 2]) terminal_exponents96)) i =
     if i %% 2 = 0 then nth witness terminal_exponents96 (i %/ 2)
     else nth witness terminal_exponents96 (i %/ 2) + 288).
  rewrite (nth_generated_figure22_pair terminal_exponents96 i).
  + rewrite size_terminal_exponents96.
    smt().
  rewrite /ell /=.
  done.
qed.

lemma figure22_indices_admissible :
  all
    (fun e => 0 <= e < ell /\ (e %% 6 = 1 \/ e %% 6 = 5))
    figure22_indices192.
proof.
  rewrite /figure22_indices192 /ell /=.
  done.
qed.

lemma figure22_index_admissible (i : int) :
  0 <= i < 192 =>
  0 <= figure22_index i < ell /\
  (figure22_index i %% 6 = 1 \/ figure22_index i %% 6 = 5).
proof.
  move=> Hi.
  have Hmem : figure22_index i \in figure22_indices192.
  + rewrite /figure22_index.
    apply (mem_nth witness figure22_indices192 i).
    rewrite size_figure22_indices192.
    exact Hi.
  have Hall := figure22_indices_admissible.
  rewrite allP in Hall.
  exact (Hall (figure22_index i) Hmem).
qed.

lemma figure22_index_range (i : int) :
  0 <= i < 192 => 0 <= figure22_index i < ell.
proof.
  move=> Hi.
  have [Hrange _] := figure22_index_admissible i Hi.
  exact Hrange.
qed.

lemma terminal_value_power96 (i : int) :
  0 <= i < 192 =>
  terminal_value i ^ 96 %% q = 2735 \/
  terminal_value i ^ 96 %% q = 723.
proof.
  move=> Hi.
  have [He Hmod] := figure22_index_admissible i Hi.
  have Hdiv := divz_eq (figure22_index i) 6.
  have Hk : 0 <= figure22_index i %/ 6 by smt().
  rewrite /terminal_value (modz_expr (zeta_root ^ figure22_index i) 96 q) 1:/#.
  rewrite -exprM.
  case Hmod => Hmod.
  + left.
    have Hexp :
      figure22_index i * 96 = (figure22_index i %/ 6) * 576 + 96 by smt().
    rewrite Hexp zeta_period_576 1:Hk 1:/#.
    by rewrite /zeta_root /q /=.
  right.
  have Hexp :
    figure22_index i * 96 = (figure22_index i %/ 6) * 576 + 480 by smt().
  rewrite Hexp zeta_period_576 1:Hk 1:/#.
  by rewrite /zeta_root /q /=.
qed.

lemma residue2735_square :
  (2735 * 2735) %% 3457 = 2734.
proof.
  rewrite (_ : 2735 * 2735 = 2163 * 3457 + 2734) 1:// modzMDl.
  done.
qed.

lemma residue723_square :
  (723 * 723) %% 3457 = 722.
proof.
  rewrite (_ : 723 * 723 = 151 * 3457 + 722) 1:// modzMDl.
  done.
qed.

lemma power192_from_power96 (x : int) :
  x ^ 192 = (x ^ 96) ^ 2.
proof.
  by rewrite (_ : 192 = 96 * 2) 1:// exprM.
qed.

lemma terminal_value_root (i : int) :
  0 <= i < 192 =>
  (terminal_value i ^ 192 - terminal_value i ^ 96 + 1) %% q = 0.
proof.
  move=> Hi.
  have H96 := terminal_value_power96 i Hi.
  case H96 => H96.
  + have Hpow := modz_expr (terminal_value i ^ 96) 2 q _; 1: done.
    rewrite H96 /q expr2 in Hpow.
    rewrite residue2735_square in Hpow.
    rewrite power192_from_power96 expr2.
    move: H96 Hpow.
    rewrite /q expr2.
    smt().
  have Hpow := modz_expr (terminal_value i ^ 96) 2 q _; 1: done.
  rewrite H96 /q expr2 in Hpow.
  rewrite residue723_square in Hpow.
  rewrite power192_from_power96 expr2.
  move: H96 Hpow.
  rewrite /q expr2.
  smt().
qed.

op omega_exp : int = 192.
op split_z_exp : int = 96.
op OMEGA_coeff : int = -886.
op ZMINUSZ5INV_coeff : int = -1665.
op NINV_coeff : int = -811.
op TWONINV_coeff : int = -1622.

lemma omega_montgomery_meaning :
  decode_mont OMEGA_coeff = (zeta_root ^ omega_exp) %% q /\
  OMEGA_coeff = centered_mont_of ((zeta_root ^ omega_exp) %% q).
proof. by rewrite /decode_mont /OMEGA_coeff /omega_exp /centered_mont_of /zeta_root /q /R /Rinv /=. qed.

lemma zminusz5inv_true_montgomery_meaning :
  decode_mont ZMINUSZ5INV_coeff = 1634 /\
  ZMINUSZ5INV_coeff = centered_mont_of 1634 /\
  (((zeta_root ^ split_z_exp - zeta_root ^ (5 * split_z_exp)) %% q) * 1634) %% q = 1.
proof.
  rewrite /decode_mont /ZMINUSZ5INV_coeff /split_z_exp.
  rewrite /centered_mont_of /zeta_root /q /R /Rinv /=.
  done.
qed.

lemma ninv_montgomery_meaning :
  decode_mont NINV_coeff = 3439 /\
  NINV_coeff = centered_mont_of 3439 /\
  (nd * 3439) %% q = 1.
proof.
  rewrite /decode_mont /NINV_coeff /centered_mont_of.
  rewrite ndE /q /R /Rinv /=.
  done.
qed.

lemma twoninv_montgomery_meaning :
  decode_mont TWONINV_coeff = 3421 /\
  TWONINV_coeff = centered_mont_of 3421 /\
  (nd * 3421) %% q = 2.
proof.
  rewrite /decode_mont /TWONINV_coeff /centered_mont_of.
  rewrite ndE /q /R /Rinv /=.
  done.
qed.

lemma forward_ntt_boundaries :
  ntt_stage1_start = 1 /\
  ntt_stage1_count = 1 /\
  ntt_radix3_start = 2 /\
  ntt_radix3_count = 4 /\
  ntt_radix2_64_start = 6 /\
  ntt_radix2_64_count = 6 /\
  ntt_radix2_32_start = 12 /\
  ntt_radix2_32_count = 12 /\
  ntt_radix2_16_start = 24 /\
  ntt_radix2_16_count = 24 /\
  ntt_radix2_8_start = 48 /\
  ntt_radix2_8_count = 48 /\
  ntt_radix2_4_start = 96 /\
  ntt_radix2_4_count = 96.
proof. by rewrite /ntt_stage1_start /ntt_stage1_count /ntt_radix3_start /ntt_radix3_count /ntt_radix2_64_start /ntt_radix2_64_count /ntt_radix2_32_start /ntt_radix2_32_count /ntt_radix2_16_start /ntt_radix2_16_count /ntt_radix2_8_start /ntt_radix2_8_count /ntt_radix2_4_start /ntt_radix2_4_count. qed.

lemma forward_ntt_total_consumption :
  ntt_stage1_count + ntt_radix3_count +
  ntt_radix2_64_count + ntt_radix2_32_count + ntt_radix2_16_count +
  ntt_radix2_8_count + ntt_radix2_4_count = 191.
proof.
  rewrite /ntt_stage1_count /ntt_radix3_count /ntt_radix2_64_count.
  rewrite /ntt_radix2_32_count /ntt_radix2_16_count /ntt_radix2_8_count.
  by rewrite /ntt_radix2_4_count.
qed.

lemma invntt_reverse_index_range (j : int) :
  0 <= j < 191 => 1 <= invntt_rev_index j <= 191.
proof.
  move=> Hj.
  rewrite /invntt_rev_index.
  smt().
qed.

lemma invntt_reverse_indexE (j : int) :
  0 <= j < 191 => invntt_rev_index j = 191 - j.
proof. by move=> _; rewrite /invntt_rev_index. qed.
