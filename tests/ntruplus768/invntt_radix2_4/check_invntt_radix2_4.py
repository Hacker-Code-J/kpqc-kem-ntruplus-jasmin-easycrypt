#!/usr/bin/env python3

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


EXPECTED_ZETAS = [
    -779, 1588, 892, -1095, -732, 294, -218, 1221, 858, -968, -1728, 354,
    1108, -275, 1709, 22, -1681, -940, 1379, 1458, -124, -1367, 1531, -1550,
    32, -1543, 274, 400, -1248, 1408, -315, 1685, -1626, -27, -1391, 417,
    1188, 1053, -1063, 1022, 251, 1401, 1501, 1409, 582, 673, 230, 361,
    -1209, 1364, 235, 444, -1247, -1341, 1206, -31, 1660, -100, 1250, 8,
    943, 443, -352, -312, 1212, 760, 871, 1322, 1130, 1473, 601, 297,
    489, 512, 514, 927, 1671, 774, 696, -1583, 432, 1640, 242, -1514,
    437, 1723, 933, 277, -1674, 559, 1655, -183, -397, -1059, 1138, 223,
]
EXPECTED_EXPORT = "jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4"
EXPECTED_HELPER = "__invntt_radix2_4_block"
EXPECTED_BASES = list(range(0, 768, 8))
EXPECTED_OFFSET = 4
MISSING_SOURCE_HINT = (
    "expected Jasmin source implementing export "
    "`jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4` at "
    "ntruplus/jasmin/768/ref/invntt_radix2_4.jazz with signature "
    "`(reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]`"
)

EXPECTED_JASMIN_SOURCE = """\
param int NTRUPLUS_N = 768;
param int NTRUPLUS_Q = 3457;
param int NTRUPLUS_QINV = 12929;
param int NTRUPLUS_BARRETT_V = 19412;
param int NTRUPLUS_BARRETT_BIAS = 33554432;
param int NTRUPLUS_ZETA96 = 223;
param int NTRUPLUS_ZETA97 = 1138;
param int NTRUPLUS_ZETA98 = -1059;
param int NTRUPLUS_ZETA99 = -397;
param int NTRUPLUS_ZETA100 = -183;
param int NTRUPLUS_ZETA101 = 1655;
param int NTRUPLUS_ZETA102 = 559;
param int NTRUPLUS_ZETA103 = -1674;
param int NTRUPLUS_ZETA104 = 277;
param int NTRUPLUS_ZETA105 = 933;
param int NTRUPLUS_ZETA106 = 1723;
param int NTRUPLUS_ZETA107 = 437;
param int NTRUPLUS_ZETA108 = -1514;
param int NTRUPLUS_ZETA109 = 242;
param int NTRUPLUS_ZETA110 = 1640;
param int NTRUPLUS_ZETA111 = 432;
param int NTRUPLUS_ZETA112 = -1583;
param int NTRUPLUS_ZETA113 = 696;
param int NTRUPLUS_ZETA114 = 774;
param int NTRUPLUS_ZETA115 = 1671;
param int NTRUPLUS_ZETA116 = 927;
param int NTRUPLUS_ZETA117 = 514;
param int NTRUPLUS_ZETA118 = 512;
param int NTRUPLUS_ZETA119 = 489;
param int NTRUPLUS_ZETA120 = 297;
param int NTRUPLUS_ZETA121 = 601;
param int NTRUPLUS_ZETA122 = 1473;
param int NTRUPLUS_ZETA123 = 1130;
param int NTRUPLUS_ZETA124 = 1322;
param int NTRUPLUS_ZETA125 = 871;
param int NTRUPLUS_ZETA126 = 760;
param int NTRUPLUS_ZETA127 = 1212;
param int NTRUPLUS_ZETA128 = -312;
param int NTRUPLUS_ZETA129 = -352;
param int NTRUPLUS_ZETA130 = 443;
param int NTRUPLUS_ZETA131 = 943;
param int NTRUPLUS_ZETA132 = 8;
param int NTRUPLUS_ZETA133 = 1250;
param int NTRUPLUS_ZETA134 = -100;
param int NTRUPLUS_ZETA135 = 1660;
param int NTRUPLUS_ZETA136 = -31;
param int NTRUPLUS_ZETA137 = 1206;
param int NTRUPLUS_ZETA138 = -1341;
param int NTRUPLUS_ZETA139 = -1247;
param int NTRUPLUS_ZETA140 = 444;
param int NTRUPLUS_ZETA141 = 235;
param int NTRUPLUS_ZETA142 = 1364;
param int NTRUPLUS_ZETA143 = -1209;
param int NTRUPLUS_ZETA144 = 361;
param int NTRUPLUS_ZETA145 = 230;
param int NTRUPLUS_ZETA146 = 673;
param int NTRUPLUS_ZETA147 = 582;
param int NTRUPLUS_ZETA148 = 1409;
param int NTRUPLUS_ZETA149 = 1501;
param int NTRUPLUS_ZETA150 = 1401;
param int NTRUPLUS_ZETA151 = 251;
param int NTRUPLUS_ZETA152 = 1022;
param int NTRUPLUS_ZETA153 = -1063;
param int NTRUPLUS_ZETA154 = 1053;
param int NTRUPLUS_ZETA155 = 1188;
param int NTRUPLUS_ZETA156 = 417;
param int NTRUPLUS_ZETA157 = -1391;
param int NTRUPLUS_ZETA158 = -27;
param int NTRUPLUS_ZETA159 = -1626;
param int NTRUPLUS_ZETA160 = 1685;
param int NTRUPLUS_ZETA161 = -315;
param int NTRUPLUS_ZETA162 = 1408;
param int NTRUPLUS_ZETA163 = -1248;
param int NTRUPLUS_ZETA164 = 400;
param int NTRUPLUS_ZETA165 = 274;
param int NTRUPLUS_ZETA166 = -1543;
param int NTRUPLUS_ZETA167 = 32;
param int NTRUPLUS_ZETA168 = -1550;
param int NTRUPLUS_ZETA169 = 1531;
param int NTRUPLUS_ZETA170 = -1367;
param int NTRUPLUS_ZETA171 = -124;
param int NTRUPLUS_ZETA172 = 1458;
param int NTRUPLUS_ZETA173 = 1379;
param int NTRUPLUS_ZETA174 = -940;
param int NTRUPLUS_ZETA175 = -1681;
param int NTRUPLUS_ZETA176 = 22;
param int NTRUPLUS_ZETA177 = 1709;
param int NTRUPLUS_ZETA178 = -275;
param int NTRUPLUS_ZETA179 = 1108;
param int NTRUPLUS_ZETA180 = 354;
param int NTRUPLUS_ZETA181 = -1728;
param int NTRUPLUS_ZETA182 = -968;
param int NTRUPLUS_ZETA183 = 858;
param int NTRUPLUS_ZETA184 = 1221;
param int NTRUPLUS_ZETA185 = -218;
param int NTRUPLUS_ZETA186 = 294;
param int NTRUPLUS_ZETA187 = -732;
param int NTRUPLUS_ZETA188 = -1095;
param int NTRUPLUS_ZETA189 = 892;
param int NTRUPLUS_ZETA190 = 1588;
param int NTRUPLUS_ZETA191 = -779;

inline fn __mul_i16(reg u16 a b) -> reg u32
{
  reg u32 ad;
  reg u32 bd;
  reg u32 c;

  ad = (32s) a;
  bd = (32s) b;
  c = ad * bd;
  return c;
}

inline fn __montgomery_reduce(reg u32 a) -> reg u16
{
  reg u16 t;
  reg u32 q;
  reg u32 td;
  reg u32 r;

  q = NTRUPLUS_Q;
  td = (32s) a;
  td *= NTRUPLUS_QINV;
  t = td;
  td = (32s) t;
  r = (32s) a;
  td *= q;
  r -= td;
  r >>s= 16;
  t = r;
  return t;
}

inline fn __barrett_reduce(reg u16 a) -> reg u16
{
  reg u16 t;
  reg u32 td;
  reg u32 v;
  reg u32 q;

  v = NTRUPLUS_BARRETT_V;
  td = (32s) a;
  td *= v;
  td += NTRUPLUS_BARRETT_BIAS;
  td >>s= 26;
  t = td;
  q = NTRUPLUS_Q;
  td = (32s) t;
  td *= q;
  t = td;
  t = a - t;
  return t;
}

#[safety =
   { requires = is_arr_init(rp,0,2 * NTRUPLUS_N)
   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)
   }
]
inline fn __invntt_radix2_4_block(
  reg mut ptr u16[NTRUPLUS_N] rp,
  reg u64 base,
  reg u16 zeta) -> reg ptr u16[NTRUPLUS_N]
{
  reg u16 low;
  reg u16 high;
  reg u16 sum;
  reg u16 diff;
  reg u16 prod;
  reg u32 acc;
  reg u64 i;
  reg u64 stop;
  reg u32 wd;
  reg u32 td;

  i = base;
  stop = base;
  stop += 4;
  while (i < stop) {
    low = rp[i];
    high = rp[i + 4];

    wd = (32s) low;
    td = (32s) high;
    wd += td;
    sum = wd;

    wd = (32s) high;
    td = (32s) low;
    wd -= td;
    diff = wd;

    sum = __barrett_reduce(sum);
    acc = __mul_i16(zeta, diff);
    prod = __montgomery_reduce(acc);
    rp[i] = sum;
    rp[i + 4] = prod;
    i += 1;
  }

  return rp;
}

#[safety =
   { requires = is_arr_init(rp,0,2 * NTRUPLUS_N)
   , ensures = is_arr_init(rp,0,2 * NTRUPLUS_N)
   }
]
#[ct = "secret → secret"]
#[sct="
{ ptr: transient, val: secret } →
{ ptr: public, val: secret }
"]
export fn jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(
  reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]
{
  _ = #init_msf();

  rp = __invntt_radix2_4_block(rp, 0, NTRUPLUS_ZETA191);
  rp = __invntt_radix2_4_block(rp, 8, NTRUPLUS_ZETA190);
  rp = __invntt_radix2_4_block(rp, 16, NTRUPLUS_ZETA189);
  rp = __invntt_radix2_4_block(rp, 24, NTRUPLUS_ZETA188);
  rp = __invntt_radix2_4_block(rp, 32, NTRUPLUS_ZETA187);
  rp = __invntt_radix2_4_block(rp, 40, NTRUPLUS_ZETA186);
  rp = __invntt_radix2_4_block(rp, 48, NTRUPLUS_ZETA185);
  rp = __invntt_radix2_4_block(rp, 56, NTRUPLUS_ZETA184);
  rp = __invntt_radix2_4_block(rp, 64, NTRUPLUS_ZETA183);
  rp = __invntt_radix2_4_block(rp, 72, NTRUPLUS_ZETA182);
  rp = __invntt_radix2_4_block(rp, 80, NTRUPLUS_ZETA181);
  rp = __invntt_radix2_4_block(rp, 88, NTRUPLUS_ZETA180);
  rp = __invntt_radix2_4_block(rp, 96, NTRUPLUS_ZETA179);
  rp = __invntt_radix2_4_block(rp, 104, NTRUPLUS_ZETA178);
  rp = __invntt_radix2_4_block(rp, 112, NTRUPLUS_ZETA177);
  rp = __invntt_radix2_4_block(rp, 120, NTRUPLUS_ZETA176);
  rp = __invntt_radix2_4_block(rp, 128, NTRUPLUS_ZETA175);
  rp = __invntt_radix2_4_block(rp, 136, NTRUPLUS_ZETA174);
  rp = __invntt_radix2_4_block(rp, 144, NTRUPLUS_ZETA173);
  rp = __invntt_radix2_4_block(rp, 152, NTRUPLUS_ZETA172);
  rp = __invntt_radix2_4_block(rp, 160, NTRUPLUS_ZETA171);
  rp = __invntt_radix2_4_block(rp, 168, NTRUPLUS_ZETA170);
  rp = __invntt_radix2_4_block(rp, 176, NTRUPLUS_ZETA169);
  rp = __invntt_radix2_4_block(rp, 184, NTRUPLUS_ZETA168);
  rp = __invntt_radix2_4_block(rp, 192, NTRUPLUS_ZETA167);
  rp = __invntt_radix2_4_block(rp, 200, NTRUPLUS_ZETA166);
  rp = __invntt_radix2_4_block(rp, 208, NTRUPLUS_ZETA165);
  rp = __invntt_radix2_4_block(rp, 216, NTRUPLUS_ZETA164);
  rp = __invntt_radix2_4_block(rp, 224, NTRUPLUS_ZETA163);
  rp = __invntt_radix2_4_block(rp, 232, NTRUPLUS_ZETA162);
  rp = __invntt_radix2_4_block(rp, 240, NTRUPLUS_ZETA161);
  rp = __invntt_radix2_4_block(rp, 248, NTRUPLUS_ZETA160);
  rp = __invntt_radix2_4_block(rp, 256, NTRUPLUS_ZETA159);
  rp = __invntt_radix2_4_block(rp, 264, NTRUPLUS_ZETA158);
  rp = __invntt_radix2_4_block(rp, 272, NTRUPLUS_ZETA157);
  rp = __invntt_radix2_4_block(rp, 280, NTRUPLUS_ZETA156);
  rp = __invntt_radix2_4_block(rp, 288, NTRUPLUS_ZETA155);
  rp = __invntt_radix2_4_block(rp, 296, NTRUPLUS_ZETA154);
  rp = __invntt_radix2_4_block(rp, 304, NTRUPLUS_ZETA153);
  rp = __invntt_radix2_4_block(rp, 312, NTRUPLUS_ZETA152);
  rp = __invntt_radix2_4_block(rp, 320, NTRUPLUS_ZETA151);
  rp = __invntt_radix2_4_block(rp, 328, NTRUPLUS_ZETA150);
  rp = __invntt_radix2_4_block(rp, 336, NTRUPLUS_ZETA149);
  rp = __invntt_radix2_4_block(rp, 344, NTRUPLUS_ZETA148);
  rp = __invntt_radix2_4_block(rp, 352, NTRUPLUS_ZETA147);
  rp = __invntt_radix2_4_block(rp, 360, NTRUPLUS_ZETA146);
  rp = __invntt_radix2_4_block(rp, 368, NTRUPLUS_ZETA145);
  rp = __invntt_radix2_4_block(rp, 376, NTRUPLUS_ZETA144);
  rp = __invntt_radix2_4_block(rp, 384, NTRUPLUS_ZETA143);
  rp = __invntt_radix2_4_block(rp, 392, NTRUPLUS_ZETA142);
  rp = __invntt_radix2_4_block(rp, 400, NTRUPLUS_ZETA141);
  rp = __invntt_radix2_4_block(rp, 408, NTRUPLUS_ZETA140);
  rp = __invntt_radix2_4_block(rp, 416, NTRUPLUS_ZETA139);
  rp = __invntt_radix2_4_block(rp, 424, NTRUPLUS_ZETA138);
  rp = __invntt_radix2_4_block(rp, 432, NTRUPLUS_ZETA137);
  rp = __invntt_radix2_4_block(rp, 440, NTRUPLUS_ZETA136);
  rp = __invntt_radix2_4_block(rp, 448, NTRUPLUS_ZETA135);
  rp = __invntt_radix2_4_block(rp, 456, NTRUPLUS_ZETA134);
  rp = __invntt_radix2_4_block(rp, 464, NTRUPLUS_ZETA133);
  rp = __invntt_radix2_4_block(rp, 472, NTRUPLUS_ZETA132);
  rp = __invntt_radix2_4_block(rp, 480, NTRUPLUS_ZETA131);
  rp = __invntt_radix2_4_block(rp, 488, NTRUPLUS_ZETA130);
  rp = __invntt_radix2_4_block(rp, 496, NTRUPLUS_ZETA129);
  rp = __invntt_radix2_4_block(rp, 504, NTRUPLUS_ZETA128);
  rp = __invntt_radix2_4_block(rp, 512, NTRUPLUS_ZETA127);
  rp = __invntt_radix2_4_block(rp, 520, NTRUPLUS_ZETA126);
  rp = __invntt_radix2_4_block(rp, 528, NTRUPLUS_ZETA125);
  rp = __invntt_radix2_4_block(rp, 536, NTRUPLUS_ZETA124);
  rp = __invntt_radix2_4_block(rp, 544, NTRUPLUS_ZETA123);
  rp = __invntt_radix2_4_block(rp, 552, NTRUPLUS_ZETA122);
  rp = __invntt_radix2_4_block(rp, 560, NTRUPLUS_ZETA121);
  rp = __invntt_radix2_4_block(rp, 568, NTRUPLUS_ZETA120);
  rp = __invntt_radix2_4_block(rp, 576, NTRUPLUS_ZETA119);
  rp = __invntt_radix2_4_block(rp, 584, NTRUPLUS_ZETA118);
  rp = __invntt_radix2_4_block(rp, 592, NTRUPLUS_ZETA117);
  rp = __invntt_radix2_4_block(rp, 600, NTRUPLUS_ZETA116);
  rp = __invntt_radix2_4_block(rp, 608, NTRUPLUS_ZETA115);
  rp = __invntt_radix2_4_block(rp, 616, NTRUPLUS_ZETA114);
  rp = __invntt_radix2_4_block(rp, 624, NTRUPLUS_ZETA113);
  rp = __invntt_radix2_4_block(rp, 632, NTRUPLUS_ZETA112);
  rp = __invntt_radix2_4_block(rp, 640, NTRUPLUS_ZETA111);
  rp = __invntt_radix2_4_block(rp, 648, NTRUPLUS_ZETA110);
  rp = __invntt_radix2_4_block(rp, 656, NTRUPLUS_ZETA109);
  rp = __invntt_radix2_4_block(rp, 664, NTRUPLUS_ZETA108);
  rp = __invntt_radix2_4_block(rp, 672, NTRUPLUS_ZETA107);
  rp = __invntt_radix2_4_block(rp, 680, NTRUPLUS_ZETA106);
  rp = __invntt_radix2_4_block(rp, 688, NTRUPLUS_ZETA105);
  rp = __invntt_radix2_4_block(rp, 696, NTRUPLUS_ZETA104);
  rp = __invntt_radix2_4_block(rp, 704, NTRUPLUS_ZETA103);
  rp = __invntt_radix2_4_block(rp, 712, NTRUPLUS_ZETA102);
  rp = __invntt_radix2_4_block(rp, 720, NTRUPLUS_ZETA101);
  rp = __invntt_radix2_4_block(rp, 728, NTRUPLUS_ZETA100);
  rp = __invntt_radix2_4_block(rp, 736, NTRUPLUS_ZETA99);
  rp = __invntt_radix2_4_block(rp, 744, NTRUPLUS_ZETA98);
  rp = __invntt_radix2_4_block(rp, 752, NTRUPLUS_ZETA97);
  rp = __invntt_radix2_4_block(rp, 760, NTRUPLUS_ZETA96);

  return rp;
}
"""


class VerificationError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise VerificationError(message)


def strip_comments(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    return re.sub(r"//.*", "", text)


def compact(text: str) -> str:
    text = re.sub(r"\s+", " ", strip_comments(text)).strip()
    text = re.sub(r"\[\s+", "[", text)
    return re.sub(r"\s+\]", "]", text)


def extract_function_body(text: str, name: str) -> str:
    match = re.search(rf"\b{name}\s*\([^)]*\)[^{{]*\{{", text)
    require(match is not None, f"could not find function `{name}`")
    start = match.end() - 1
    depth = 0
    for index in range(start, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start + 1 : index]
    raise VerificationError(f"unterminated body for function `{name}`")


def parse_c_zetas(text: str) -> list[int]:
    match = re.search(r"const\s+int16_t\s+zetas\s*\[\s*192\s*\]\s*=\s*\{(.*?)\};", text, flags=re.S)
    require(match is not None, "could not find the 192-entry C zetas table")
    return [int(token) for token in re.findall(r"-?\d+", match.group(1))]


def parse_inv_tail_schedule() -> tuple[int, int, list[int]]:
    step4_blocks = 768 // (2 * EXPECTED_OFFSET)
    return 191, step4_blocks, [block * (EXPECTED_OFFSET << 1) for block in range(step4_blocks)]


def verify_c_text(text: str) -> None:
    zetas = parse_c_zetas(text)
    require(len(zetas) == 192, f"expected 192 C twiddles, found {len(zetas)}")
    require(
        list(reversed(zetas[96:192])) == EXPECTED_ZETAS,
        f"expected reversed C zetas[96:192] == {EXPECTED_ZETAS}, found {list(reversed(zetas[96:192]))}",
    )

    body = compact(extract_function_body(text, "invntt"))
    copy_prefix = re.compile(
        r"int16_t t1, t2, t3; int16_t zeta1, zeta2; int k = 191; "
        r"for \(int i = 0; i < NTRUPLUS_N; i\+\+\) \{ r\[i\] = a\[i\]; \} "
    )
    prefix_match = copy_prefix.search(body)
    require(prefix_match is not None, "C invntt() no longer copies input into the working output before the inverse radix-2 tail")

    stage = re.compile(
        r"for \(int step = 4; step <= 64; step <<= 1\) \{ "
        r"for \(int start = 0; start < NTRUPLUS_N; start \+= \(step << 1\)\) \{ "
        r"zeta1 = zetas\[k--\]; "
        r"for \(int i = start; i < start \+ step; i\+\+\) \{ "
        r"t1 = r\[i \+ step\]; "
        r"r\[i \+ step\] = fqmul\(zeta1, t1 - r\[i\]\); "
        r"r\[i\] = barrett_reduce\(r\[i\] \+ t1\); \} \} \}"
    )
    stage_match = stage.search(body)
    require(
        stage_match is not None,
        "C invntt() radix-2 head no longer matches the verified step=4->8->16->32->64 schedule and fqmul/barrett flow",
    )
    require(
        prefix_match.end() <= stage_match.start(),
        "C invntt() no longer executes the copy prefix before the inverse radix-2 head",
    )

    start_index, block_count, bases = parse_inv_tail_schedule()
    require(start_index == 191, f"derived C inverse step4 zeta start changed from 191 to {start_index}")
    require(block_count == 96, f"derived C inverse step4 block count changed from 96 to {block_count}")
    require(bases == EXPECTED_BASES, f"derived C inverse step4 bases changed: expected {EXPECTED_BASES}, found {bases}")


def verify_jasmin_text(text: str) -> None:
    source = compact(text)
    for name, value in (
        ("NTRUPLUS_N", 768),
        ("NTRUPLUS_Q", 3457),
        ("NTRUPLUS_QINV", 12929),
        ("NTRUPLUS_BARRETT_V", 19412),
        ("NTRUPLUS_BARRETT_BIAS", 33554432),
    ):
        require(
            re.search(rf"param int {name} = {value};", source) is not None,
            f"Jasmin inverse radix-2 slice must fix {name} == {value}",
        )
    for index in range(96, 192):
        value = EXPECTED_ZETAS[191 - index]
        require(
            re.search(rf"param int NTRUPLUS_ZETA{index} = {value};", source) is not None,
            f"Jasmin inverse radix-2 slice must fix NTRUPLUS_ZETA{index} == {value}",
        )

    require(f"export fn {EXPECTED_EXPORT}(" in source, f"missing expected Jasmin export `{EXPECTED_EXPORT}`")
    require(f"inline fn {EXPECTED_HELPER}(" in source, f"missing expected Jasmin helper `{EXPECTED_HELPER}`")

    require(
        re.search(
            rf"export fn {EXPECTED_EXPORT}\(\s*reg mut ptr u16\[NTRUPLUS_N\] rp\s*\) -> reg ptr u16\[NTRUPLUS_N\]",
            text,
            flags=re.S,
        )
        is not None,
        MISSING_SOURCE_HINT,
    )

    mul_body = compact(extract_function_body(text, "__mul_i16"))
    require(
        re.fullmatch(
            r"reg u32 ad; reg u32 bd; reg u32 c; ad = \(32s\) a; bd = \(32s\) b; c = ad \* bd; return c;",
            mul_body,
        )
        is not None,
        "Jasmin signed 16x16 multiply helper no longer matches the verified data flow",
    )

    montgomery_body = compact(extract_function_body(text, "__montgomery_reduce"))
    require(
        re.fullmatch(
            r"reg u16 t; reg u32 q; reg u32 td; reg u32 r; "
            r"q = NTRUPLUS_Q; td = \(32s\) a; td \*= NTRUPLUS_QINV; t = td; "
            r"td = \(32s\) t; r = \(32s\) a; td \*= q; r -= td; r >>s= 16; t = r; return t;",
            montgomery_body,
        )
        is not None,
        "Jasmin Montgomery reducer no longer matches the verified Q/QINV data flow",
    )

    barrett_body = compact(extract_function_body(text, "__barrett_reduce"))
    require(
        re.fullmatch(
            r"reg u16 t; reg u32 td; reg u32 v; reg u32 q; "
            r"v = NTRUPLUS_BARRETT_V; td = \(32s\) a; td \*= v; td \+= NTRUPLUS_BARRETT_BIAS; "
            r"td >>s= 26; t = td; q = NTRUPLUS_Q; td = \(32s\) t; td \*= q; t = td; t = a - t; return t;",
            barrett_body,
        )
        is not None,
        "Jasmin Barrett reducer no longer matches the verified rounding and subtraction data flow",
    )

    helper_body = compact(extract_function_body(text, EXPECTED_HELPER))
    helper_pattern = re.compile(
        r"reg u16 low; reg u16 high; reg u16 sum; reg u16 diff; reg u16 prod; "
        r"reg u32 acc; reg u64 i; reg u64 stop; reg u32 wd; reg u32 td; "
        r"i = base; stop = base; stop \+= 4; while \(i < stop\) \{ "
        r"low = rp\[i\]; high = rp\[i \+ 4\]; "
        r"wd = \(32s\) low; td = \(32s\) high; wd \+= td; sum = wd; "
        r"wd = \(32s\) high; td = \(32s\) low; wd -= td; diff = wd; "
        r"sum = __barrett_reduce\(sum\); "
        r"acc = __mul_i16\(zeta, diff\); prod = __montgomery_reduce\(acc\); "
        r"rp\[i\] = sum; rp\[i \+ 4\] = prod; i \+= 1; \} return rp;"
    )
    require(
        helper_pattern.search(helper_body) is not None,
        "Jasmin inverse radix-2 helper no longer matches the verified in-place step=4 flow",
    )

    export_body = compact(extract_function_body(text, EXPECTED_EXPORT))
    expected_calls = " ".join(
        f"rp = {EXPECTED_HELPER}(rp, {base}, NTRUPLUS_ZETA{index});"
        for index, base in zip(range(191, 95, -1), EXPECTED_BASES, strict=True)
    )
    call_pattern = re.compile(rf"_ = #init_msf\(\); {re.escape(expected_calls)} return rp;")
    require(
        call_pattern.search(export_body) is not None,
        "Jasmin inverse radix-2 export no longer matches the verified 96-block descending-zeta schedule",
    )


def expect_rejected(check, text: str, label: str) -> None:
    try:
        check(text)
    except VerificationError:
        return
    raise VerificationError(f"checker accepted negative mutation: {label}")


def run_self_check(c_text: str) -> None:
    verify_c_text(c_text)
    verify_jasmin_text(EXPECTED_JASMIN_SOURCE)

    mutated_c_zeta_window = c_text.replace(
        " 1221,  -218,   294,  -732, -1095,   892,  1588,  -779",
        " 1221,  -218,   294,  -732, -1095,  1588,   892,  -779",
        1,
    )
    require(mutated_c_zeta_window != c_text, "could not construct C inverse step4 zeta-order mutation")
    expect_rejected(verify_c_text, mutated_c_zeta_window, "C wrong inverse step4 zeta order")

    mutated_c_tail = c_text.replace(
        "for (int step = 4; step <= 64; step <<= 1)",
        "for (int step = 8; step <= 64; step <<= 1)",
        1,
    )
    require(mutated_c_tail != c_text, "could not construct C inverse tail-depth mutation")
    expect_rejected(verify_c_text, mutated_c_tail, "C inverse radix-2 head no longer starts at step4")

    mutated_c_output = c_text.replace(
        "r[i + step] = fqmul(zeta1, t1 - r[i]);",
        "r[i + step] = fqmul(zeta1, r[i] - t1);",
        1,
    )
    require(mutated_c_output != c_text, "could not construct C inverse high-output mutation")
    expect_rejected(verify_c_text, mutated_c_output, "C inverse high output uses wrong fqmul input")

    mutated_jasmin_zeta = EXPECTED_JASMIN_SOURCE.replace("NTRUPLUS_ZETA191 = -779", "NTRUPLUS_ZETA191 = 1588", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_zeta, "Jasmin wrong inverse fixed twiddle")

    mutated_jasmin_alias = EXPECTED_JASMIN_SOURCE.replace("low = rp[i];", "low = ap[i];", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_alias, "Jasmin inverse helper no longer reads in-place state")

    mutated_jasmin_offset = EXPECTED_JASMIN_SOURCE.replace("high = rp[i + 4];", "high = rp[i + 8];", 1)
    expect_rejected(verify_jasmin_text, mutated_jasmin_offset, "Jasmin inverse helper uses wrong pair offset")

    mutated_jasmin_schedule = EXPECTED_JASMIN_SOURCE.replace(
        "rp = __invntt_radix2_4_block(rp, 0, NTRUPLUS_ZETA191);\n"
        "  rp = __invntt_radix2_4_block(rp, 8, NTRUPLUS_ZETA190);",
        "rp = __invntt_radix2_4_block(rp, 8, NTRUPLUS_ZETA190);\n"
        "  rp = __invntt_radix2_4_block(rp, 0, NTRUPLUS_ZETA191);",
        1,
    )
    expect_rejected(verify_jasmin_text, mutated_jasmin_schedule, "Jasmin inverse helper-call schedule is permuted")

    stale_two_buffer_copy = EXPECTED_JASMIN_SOURCE.replace(
        "inline fn __invntt_radix2_4_block(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg u64 base,",
        "inline fn __invntt_radix2_4_block(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg ptr u16[NTRUPLUS_N] ap,\n  reg u64 base,",
        1,
    )
    stale_two_buffer_copy = stale_two_buffer_copy.replace("low = rp[i];", "low = ap[i];", 1)
    stale_two_buffer_copy = stale_two_buffer_copy.replace("high = rp[i + 4];", "high = ap[i + 4];", 1)
    stale_two_buffer_copy = stale_two_buffer_copy.replace("export fn jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(\n  reg mut ptr u16[NTRUPLUS_N] rp) -> reg ptr u16[NTRUPLUS_N]", "export fn jade_ntruplus_ntruplus768_amd64_ref_invntt_radix2_4(\n  reg mut ptr u16[NTRUPLUS_N] rp,\n  reg ptr u16[NTRUPLUS_N] ap) -> reg ptr u16[NTRUPLUS_N]", 1)
    stale_two_buffer_copy = stale_two_buffer_copy.replace("rp = __invntt_radix2_4_block(rp, 0, NTRUPLUS_ZETA191);", "rp = __invntt_radix2_4_block(rp, ap, 0, NTRUPLUS_ZETA191);", 1)
    expect_rejected(verify_jasmin_text, stale_two_buffer_copy, "Jasmin accepted stale two-buffer inverse copy")


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Tie the standalone Jasmin NTRU+768 inverse radix-2 step4 slice to the C inverse loop."
    )
    parser.add_argument("--c-source", required=True, help="path to NTRU+/NTRU+768/ntt.c")
    parser.add_argument("--jasmin-source", required=True, help="path to invntt_radix2_4.jazz")
    parser.add_argument("--self-check", action="store_true", help="also require representative bad mutations to be rejected")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    try:
        c_text = Path(args.c_source).read_text(encoding="utf-8")
        verify_c_text(c_text)

        jasmin_path = Path(args.jasmin_source)
        if jasmin_path.exists():
            jasmin_text = jasmin_path.read_text(encoding="utf-8")
            verify_jasmin_text(jasmin_text)
        elif args.self_check:
            jasmin_text = EXPECTED_JASMIN_SOURCE
            verify_jasmin_text(jasmin_text)
        else:
            raise VerificationError(f"{MISSING_SOURCE_HINT}; missing file `{jasmin_path}`")

        if args.self_check:
            run_self_check(c_text)
    except (OSError, VerificationError, ValueError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1

    if args.self_check:
        print("PASS: NTRU+768 inverse radix-2 step4 checker rejected representative bad mutations")
    print("PASS: NTRU+768 inverse radix-2 step4 C/Jasmin source coupling")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
