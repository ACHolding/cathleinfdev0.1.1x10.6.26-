#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cathle 0.1x — single-file N64 emulator monolith
Engine: cathle
Audio engine: cathle-audio (live host output via pygame-ce SDL2 AudioDevice + math soft-clip/resample)
VR4300 opcode surface complete (integer/FPU/COP0 + RI/CU traps).
HLE OS patches (OP_PATCH/OP_GROUP), signature scan, game profiles,
OS/RSP/RDP/PIF HLE (Python 3.14).
HLE IPL3 boot + signature patch install for commercial titles (SM64 first; Fast3D/F3DEX2 soft RDP).

Note on ContraSF Corn: Corn's source was never released (closed-source Win32).
This tree cannot literally import Corn; SM64-first HLE + soft RDP follows the
same commercial-boot goals while keeping the cathle Tk GUI.

Single-file Python 3.14 — Tkinter, no external assets
Run: python3 ####cathle1.x10.6.26.py --self-test
"""
from __future__ import annotations
import array, base64, math, os, platform, struct, sys, time, random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple, Callable, Any
import threading

_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
_DEFAULT_ROM_DIR = os.path.join(_SCRIPT_DIR, "Roms")
_ROM_SCAN_MAX_FILES = 512
try:
    import tkinter as tk
    from tkinter import filedialog, messagebox, simpledialog, ttk
except ImportError:
    tk = filedialog = messagebox = simpledialog = ttk = None

APP_NAME = "cathle 0.1x"
VERSION = "0.1x"; ENGINE_NAME = "cathle"; PYTHON_TARGET = "3.14"
WINDOW_TITLE = "cathle 0.1x"
COPYRIGHT_LINE = "[c] 1999-2026 nintendo  [c] 1999-2026 ac kondo solutions"
DEBUG_BANNER = f"{APP_NAME} - {COPYRIGHT_LINE}"
ROM_EXTENSIONS = (".z64", ".v64", ".n64", ".rom", ".bin")
# cathle ROM browser columns (Name / Country / Size / Filename / Comments).
ROM_BROWSER_COLUMNS = (
    ("good_name", "Name", 220),
    ("country", "Country", 70),
    ("rom_size", "Size", 72),
    ("file_name", "Filename", 160),
    ("comments", "Comments", 240),
)

CATHLE_WIN_GRAY = CATHLE_WIN_FACE = CATHLE_BTN_FACE = "#d4d0c8"
CATHLE_BTN_HIGHLIGHT = "#ffffff"; CATHLE_BTN_SHADOW = "#808080"
CATHLE_BTN_DKSHADOW = "#404040"
CATHLE_PANEL_WHITE = "#ffffff"; CATHLE_TEXT = "#000000"; CATHLE_SPLASH_GRAY = "#808080"
CATHLE_VIEWPORT_BORDER = "#808080"; CATHLE_LIST_SEL_BG = "#000080"; CATHLE_LIST_SEL_FG = "#ffffff"
BG_COLOR, PANEL_COLOR, TEXT_COLOR = CATHLE_WIN_GRAY, CATHLE_BTN_FACE, CATHLE_TEXT
ACCENT_BLUE, TERMINAL_GREEN, STATUS_RED, WHITE = CATHLE_TEXT, "#008000", "#800000", CATHLE_PANEL_WHITE
def _cathle_ui_fonts():
    if platform.system() == "Darwin": return ("Tahoma",11),("Courier New",11),("Tahoma",11,"bold")
    if platform.system() == "Windows": return ("MS Sans Serif",8),("Courier New",9),("MS Sans Serif",8,"bold")
    return ("TkDefaultFont",9),("Courier New",9),("TkDefaultFont",9,"bold")
UI_FONT, UI_FONT_MONO, UI_FONT_BOLD = _cathle_ui_fonts()

RDRAM_SIZE = 8*1024*1024; RDRAM_SIZE_4MB = 4*1024*1024
RSP_DMEM_SIZE = 0x1000; RSP_IMEM_SIZE = 0x1000; PIF_RAM_SIZE = 0x40
EEPROM_4K_SIZE = 0x200; EEPROM_16K_SIZE = 0x800; SRAM_SIZE = 0x8000; FLASHRAM_SIZE = 0x20000
MASK_8 = 0xFF; MASK_16 = 0xFFFF; MASK_32 = 0xFFFFFFFF; MASK_64 = 0xFFFFFFFFFFFFFFFF
# N64 timing — VR4300 @ 93.75 MHz, NTSC VI @ 60 Hz (PAL @ 50 Hz).
N64_CPU_HZ = 93_750_000
N64_VI_NTSC_HZ = 60
N64_VI_PAL_HZ = 50
N64_CYCLES_PER_FRAME_NTSC = N64_CPU_HZ // N64_VI_NTSC_HZ  # 1_562_500
N64_CYCLES_PER_FRAME_PAL = N64_CPU_HZ // N64_VI_PAL_HZ
FRAME_PERIOD_NTSC = 1.0 / N64_VI_NTSC_HZ  # 1/60 s — real N64 NTSC frame
FRAME_PERIOD_PAL = 1.0 / N64_VI_PAL_HZ
# Host speed: 1.0 = real N64 (lock VI rate to 60/50 Hz). Higher = faster than console.
EMU_SPEED_N64 = 1.0
DEFAULT_EMU_SPEED = EMU_SPEED_N64
# Pure-Python interpreter budget per displayed frame (~85% of a 60 Hz period).
INTERP_FRAME_BUDGET_S = FRAME_PERIOD_NTSC * 0.85  # ≈ 0.01417 s
INTERP_MIN_STEPS = 12_000
INTERP_MAX_STEPS = 200_000
INTERP_BOOT_STEPS = 80_000  # CORN-style SM64-first: burn CPU until first lit frame
# UI present cadence matches NTSC VI (ms between Tk poll/blit ticks).
UI_POLL_MS = max(1, 1000 // N64_VI_NTSC_HZ)  # 16 ms → 60 Hz
def u8(v): return v & MASK_8
def u16(v): return v & MASK_16
def u32(v): return v & MASK_32
def u64(v): return v & MASK_64
def sign8(v): v &= MASK_8; return v - 0x100 if v & 0x80 else v
def sign16(v): v &= MASK_16; return v - 0x10000 if v & 0x8000 else v
def sign32(v): v &= MASK_32; return v - 0x100000000 if v & 0x80000000 else v
def sign64(v): v &= MASK_64; return v - 0x10000000000000000 if v & 0x8000000000000000 else v
def sx8_to_64(v): return u64(sign8(v))
def sx16_to_64(v): return u64(sign16(v))
def sx32_to_64(v): return u64(sign32(v))
def be32(data, off):
    if off < 0 or off + 3 >= len(data): return 0
    return struct.unpack_from(">I", data, off)[0]
def put_be32(data, off, val):
    if off < 0 or off + 3 >= len(data): return
    struct.pack_into(">I", data, off, val & MASK_32)
def be64(data, off):
    if off < 0 or off + 7 >= len(data): return 0
    return struct.unpack_from(">Q", data, off)[0]
def put_be64(data, off, val):
    if off < 0 or off + 7 >= len(data): return
    struct.pack_into(">Q", data, off, val & MASK_64)
_S_U32 = struct.Struct(">I"); _S_F32 = struct.Struct(">f")
_S_U64 = struct.Struct(">Q"); _S_F64 = struct.Struct(">d"); _S_U16 = struct.Struct(">H")
def f32_to_bits(v, _pf=_S_F32.pack, _ui=_S_U32.unpack):
    try:
        return _ui(_pf(float(v)))[0]
    except (OverflowError, ValueError):
        return 0x7F800000 if float(v) > 0.0 else 0xFF800000
def bits_to_f32(v, _pi=_S_U32.pack, _uf=_S_F32.unpack): return _uf(_pi(v & MASK_32))[0]
def f64_to_bits(v):
    try:
        return struct.unpack(">Q", struct.pack(">d", float(v)))[0]
    except (OverflowError, ValueError):
        return 0x7FF0000000000000 if float(v) > 0.0 else 0xFFF0000000000000
def bits_to_f64(v): return struct.unpack(">d", struct.pack(">Q", v & MASK_64))[0]

# ── N64 hardware register map ──
SP_MEM_ADDR=0x04040000; SP_DRAM_ADDR=0x04040004; SP_RD_LEN=0x04040008; SP_WR_LEN=0x0404000C
SP_STATUS=0x04040010; SP_DMA_FULL=0x04040014; SP_DMA_BUSY=0x04040018; SP_SEMAPHORE=0x0404001C
SP_PC=0x04080000; SP_IBIST=0x04080004
SP_STATUS_HALT=0x0001; SP_STATUS_BROKE=0x0002; SP_STATUS_DMA_BUSY=0x0004; SP_STATUS_DMA_FULL=0x0008
SP_STATUS_IO_FULL=0x0010; SP_STATUS_SSTEP=0x0020; SP_STATUS_INTR_BREAK=0x0040
SP_CLR_HALT=0x0001; SP_SET_HALT=0x0002; SP_CLR_BROKE=0x0004; SP_CLR_INTR=0x0008; SP_SET_INTR=0x0010
SP_CLR_SSTEP=0x0020; SP_SET_SSTEP=0x0040; SP_CLR_INTR_BREAK=0x0080; SP_SET_INTR_BREAK=0x0100
SP_CLR_SIG0=0x0200; SP_SET_SIG0=0x0400; SP_CLR_SIG1=0x0800; SP_SET_SIG1=0x1000
SP_CLR_SIG2=0x2000; SP_SET_SIG2=0x4000; SP_CLR_SIG3=0x00010000; SP_SET_SIG3=0x00020000
SP_CLR_SIG4=0x00040000; SP_SET_SIG4=0x00080000; SP_CLR_SIG5=0x00100000; SP_SET_SIG5=0x00200000
SP_CLR_SIG6=0x00400000; SP_SET_SIG6=0x00800000; SP_CLR_SIG7=0x01000000; SP_SET_SIG7=0x02000000
DPC_START=0x04100000; DPC_END=0x04100004; DPC_CURRENT=0x04100008; DPC_STATUS=0x0410000C
DPC_CLOCK=0x04100010; DPC_BUFBUSY=0x04100014; DPC_PIPEBUSY=0x04100018; DPC_TMEM=0x0410001C
DPC_STATUS_XBUS_DMEM_DMA=0x0001; DPC_STATUS_FREEZE=0x0002; DPC_STATUS_FLUSH=0x0004
DPC_CLR_XBUS_DMEM_DMA=0x0001; DPC_SET_XBUS_DMEM_DMA=0x0002; DPC_CLR_FREEZE=0x0004; DPC_SET_FREEZE=0x0008
DPC_CLR_FLUSH=0x0010; DPC_SET_FLUSH=0x0020
DPS_TBIST=0x04200000; DPS_TEST_MODE=0x04200004; DPS_BUFTEST=0x04200008; DPS_DETAIL=0x0420000C
MI_MODE=0x04300000; MI_VERSION=0x04300004; MI_INTR=0x04300008; MI_INTR_MASK=0x0430000C
# MI_MODE read: [6:0] init length, 7 init, 8 ebus test, 9 RDRAM reg mode.
MI_MODE_INIT=0x0080; MI_MODE_EBUS=0x0100; MI_MODE_RDRAM=0x0200
# MI_MODE write: [6:0] init length, 7/8 clr/set init, 9/10 clr/set ebus, 11 clr DP intr, 12/13 clr/set RDRAM.
MI_CLR_INIT=0x0080; MI_SET_INIT=0x0100; MI_CLR_EBUS=0x0200; MI_SET_EBUS=0x0400; MI_CLR_DP_INTR=0x0800
MI_CLR_RDRAM=0x1000; MI_SET_RDRAM=0x2000
MI_INTR_SP=0x01; MI_INTR_SI=0x02; MI_INTR_AI=0x04; MI_INTR_VI=0x08; MI_INTR_PI=0x10; MI_INTR_DP=0x20
MI_INTR_MASK_CLR_SP=0x0001; MI_INTR_MASK_SET_SP=0x0002; MI_INTR_MASK_CLR_SI=0x0004; MI_INTR_MASK_SET_SI=0x0008
MI_INTR_MASK_CLR_AI=0x0010; MI_INTR_MASK_SET_AI=0x0020; MI_INTR_MASK_CLR_VI=0x0040; MI_INTR_MASK_SET_VI=0x0080
MI_INTR_MASK_CLR_PI=0x0100; MI_INTR_MASK_SET_PI=0x0200; MI_INTR_MASK_CLR_DP=0x0400; MI_INTR_MASK_SET_DP=0x0800
VI_STATUS=0x04400000; VI_ORIGIN=0x04400004; VI_WIDTH=0x04400008; VI_INTR=0x0440000C
VI_V_CURRENT=0x04400010; VI_BURST=0x04400014; VI_V_SYNC=0x04400018; VI_H_SYNC=0x0440001C
VI_LEAP=0x04400020; VI_H_START=0x04400024; VI_V_START=0x04400028; VI_V_BURST=0x0440002C
VI_X_SCALE=0x04400030; VI_Y_SCALE=0x04400034
AI_DRAM_ADDR=0x04500000; AI_LEN=0x04500004; AI_CONTROL=0x04500008; AI_STATUS=0x0450000C
AI_DACRATE=0x04500010; AI_BITRATE=0x04500014
AI_STATUS_FIFO_FULL=0x80000000; AI_STATUS_DMA_BUSY=0x40000000
PI_DRAM_ADDR=0x04600000; PI_CART_ADDR=0x04600004; PI_RD_LEN=0x04600008; PI_WR_LEN=0x0460000C
PI_STATUS=0x04600010; PI_DOM1_LAT=0x04600014; PI_DOM1_PWD=0x04600018; PI_DOM1_PGS=0x0460001C
PI_DOM1_RLS=0x04600020; PI_DOM2_LAT=0x04600024; PI_DOM2_PWD=0x04600028; PI_DOM2_PGS=0x0460002C
PI_DOM2_RLS=0x04600030; PI_STATUS_DMA_BUSY=0x0001
RI_MODE=0x04700000; RI_CONFIG=0x04700004; RI_CURRENT_LOAD=0x04700008; RI_SELECT=0x0470000C
RI_REFRESH=0x04700010; RI_LATENCY=0x04700014; RI_RERROR=0x04700018; RI_WERROR=0x0470001C
SI_DRAM_ADDR=0x04800000; SI_PIF_ADDR_RD=0x04800004; SI_PIF_ADDR_WR=0x04800010; SI_STATUS=0x04800018
SI_STATUS_INTERRUPT=0x1000; SI_STATUS_DMA_BUSY=0x2000

CP0_INDEX=0; CP0_RANDOM=1; CP0_ENTRYLO0=2; CP0_ENTRYLO1=3; CP0_CONTEXT=4; CP0_PAGEMASK=5; CP0_WIRED=6
CP0_BADVADDR=8; CP0_COUNT=9; CP0_ENTRYHI=10; CP0_COMPARE=11; CP0_STATUS=12; CP0_CAUSE=13; CP0_EPC=14
CP0_PRID=15; CP0_CONFIG=16; CP0_LLADDR=17; CP0_ERROREPC=30
STATUS_FR=0x04000000; STATUS_IE=0x0001; STATUS_EXL=0x0002; STATUS_ERL=0x0004; STATUS_BEV=0x00400000; STATUS_CU1=0x20000000
STATUS_IM2=0x0400  # RCP / MI interrupt enable in Status
CAUSE_IP2=0x0400; CAUSE_IP7=0x8000  # timer
CAUSE_BD=0x80000000
# COUNT units (half the 93.75 MHz CPU clock) per second, and per VI frame.
N64_COUNT_HZ = N64_CPU_HZ // 2
VI_CLOCK_NTSC = 48_681_812; VI_CLOCK_PAL = 49_656_530; VI_CLOCK_MPAL = 48_628_316
SP_STATUS_SIG2_TASKDONE = 0x0200
FCR31_COND_BIT=23
FCR31_CAUSE_INEXACT=0x01; FCR31_CAUSE_UNDERFLOW=0x02; FCR31_CAUSE_OVERFLOW=0x04; FCR31_CAUSE_DIVBYZERO=0x08; FCR31_CAUSE_INVALID=0x10

# ── N64 CIC chip detection ──
CIC_NUS_6101,CIC_NUS_6102,CIC_NUS_6103,CIC_NUS_6105,CIC_NUS_6106 = 0,1,2,3,4
CIC_NUS_5167,CIC_NUS_8303,CIC_NUS_8401,CIC_NUS_DDUS,CIC_NUS_XENO = 5,6,7,8,9
CIC_NUS_7102 = 10
SAVE_AUTO=0; SAVE_EEPROM_4K=1; SAVE_EEPROM_16K=2; SAVE_SRAM=3; SAVE_FLASHRAM=4
REGION_NTSC=0; REGION_PAL=1; REGION_MPAL=2
# CIC is identified by CRC32 of the cart's IPL3 (ROM 0x40..0x1000). PAL 7101/7103/
# 7105/7106 ship the same IPL3 as 6102/6103/6105/6106; only 7102 (Lylat Wars) differs.
CIC_IPL3_CRC32 = {
    0x6170A4A1: CIC_NUS_6101, 0x009E9EA3: CIC_NUS_7102, 0x90BB6CB5: CIC_NUS_6102,
    0x0B050EE0: CIC_NUS_6103, 0x98BC2C86: CIC_NUS_6105, 0xACC8580A: CIC_NUS_6106,
    0x0E018159: CIC_NUS_8303, 0x10C68B18: CIC_NUS_8401, 0xBC605D0A: CIC_NUS_DDUS,
    0x5C124E9C: CIC_NUS_5167,
}
# Seed byte (IPL3 s6 / PIF RAM 0x26) per CIC.
CIC_SEEDS = {CIC_NUS_6101: 0x3F, CIC_NUS_7102: 0x3F, CIC_NUS_6102: 0x3F, CIC_NUS_6103: 0x78,
             CIC_NUS_6105: 0x91, CIC_NUS_6106: 0x85, CIC_NUS_8303: 0xDD, CIC_NUS_8401: 0xDD,
             CIC_NUS_DDUS: 0xDE, CIC_NUS_5167: 0xDD}

def identify_cic(rom) -> Tuple[int, bool]:
    """(cic, known) from the IPL3 CRC32; unknown IPL3 falls back to 6102."""
    import zlib
    if len(rom) < 0x1000: return CIC_NUS_6102, False
    cic = CIC_IPL3_CRC32.get(zlib.crc32(bytes(rom[0x40:0x1000])) & MASK_32)
    return (cic, True) if cic is not None else (CIC_NUS_6102, False)

def get_cic_chip_id(rom):
    return identify_cic(rom)[0]

def recalculate_crcs(data):
    CRC_SRC_SIZE = 0x00101000
    if len(data) < 0x1000: return 0, 0
    chip = get_cic_chip_id(data)
    seeds = {CIC_NUS_6101: 0xF8CA4DDC, CIC_NUS_7102: 0xF8CA4DDC, CIC_NUS_6102: 0xF8CA4DDC, CIC_NUS_6103: 0xA3886759,
             CIC_NUS_6105: 0xDF26F436, CIC_NUS_6106: 0x1FEA617A}
    seed = seeds.get(chip, 0xF8CA4DDC)
    t1 = t2 = t3 = t4 = t5 = t6 = seed
    ds = len(data)
    limit = min(CRC_SRC_SIZE, ds)
    is_6105 = chip == CIC_NUS_6105
    for i in range(0x1000, limit, 4):
        d = be32(data, i) if i + 3 < ds else 0
        if (t6 + d) < t6: t4 += 1
        t6 = u32(t6 + d); t3 ^= d
        shift = d & 0x1F
        r = (d << shift) | (d >> (32 - shift)) if shift else d
        t5 = u32(t5 + r)
        if t2 > d: t2 ^= r
        else: t2 ^= t6 ^ d
        if is_6105:
            jd = be32(data, 0x0750 + (i & 0xFF)) if 0x0753 + (i & 0xFF) < ds else 0
            t1 = u32(t1 + (jd ^ d))
        else:
            t1 = u32(t1 + (t5 ^ d))
    if chip == CIC_NUS_6103: crc0 = u32((t6 ^ t4) + t3); crc1 = u32((t5 ^ t2) + t1)
    elif chip == CIC_NUS_6106: crc0 = u32((t6 * t4) + t3); crc1 = u32((t5 * t2) + t1)
    else: crc0 = u32(t6 ^ t4 ^ t3); crc1 = u32(t5 ^ t2 ^ t1)
    return crc0, crc1

Z64_MAGIC = b"\x80\x37\x12\x40"; V64_MAGIC = b"\x37\x80\x40\x12"; N64_LE_MAGIC = b"\x40\x12\x37\x80"
_CART_SIGS = (Z64_MAGIC, V64_MAGIC, N64_LE_MAGIC)

def strip_documentation_header(data):
    if len(data) < 4: return
    if data[0:4] in _CART_SIGS: return
    cap = min(len(data), 16 * 1024 * 1024)
    for off in (4096, 2048, 512):
        if off + 4 <= cap and data[off:off + 4] in _CART_SIGS:
            del data[:off]; return

def apply_cart_header_defaults(data):
    if len(data)<0x40: data.extend(b"\x00"*(0x40-len(data)))
    if data[0:4] not in _CART_SIGS or data[0:4]!=Z64_MAGIC: return
    if be32(data,0x04)==0: put_be32(data,0x04,0x00000F48)
    boot=be32(data,0x08)
    if boot==0 or boot==MASK_32: put_be32(data,0x08,0x80000400)
    if be32(data,0x0C)==0: put_be32(data,0x0C,0x0000144B)
    title=data[0x20:0x34]
    if not any(title): data[0x20:0x34]=b"Ultra 64\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"[:20].ljust(20,b"\x00")
    # Only fill a missing checksum — never rewrite a real cart's CRC1/CRC2 (they are its identity).
    if be32(data,0x10)==0 and be32(data,0x14)==0:
        c1,c2=recalculate_crcs(data); put_be32(data,0x10,c1); put_be32(data,0x14,c2)

def normalize_rom_bytes(data):
    data=bytearray(data); strip_documentation_header(data)
    if len(data)<4: return data
    m=data[0:4]
    if m==V64_MAGIC:
        for i in range(0,len(data)-1,2): data[i],data[i+1]=data[i+1],data[i]
        apply_cart_header_defaults(data); return data
    if m==N64_LE_MAGIC:
        for i in range(0,len(data)-3,4):
            data[i],data[i+3]=data[i+3],data[i]; data[i+1],data[i+2]=data[i+2],data[i+1]
        apply_cart_header_defaults(data); return data
    if m==Z64_MAGIC: apply_cart_header_defaults(data); return data
    return data

def read_rom_file(path: str, limit: Optional[int] = None) -> bytes:
    """Raw ROM bytes from a dump or from the first ROM-like member of a .zip archive."""
    import zipfile
    if zipfile.is_zipfile(path):
        with zipfile.ZipFile(path) as zf:
            members = [i for i in zf.infolist() if not i.is_dir()]
            roms = [i for i in members if i.filename.lower().endswith(ROM_EXTENSIONS)] or members
            if not roms:
                raise OSError("zip archive contains no files")
            best = max(roms, key=lambda i: i.file_size)
            with zf.open(best) as fh:
                return fh.read(limit) if limit else fh.read()
    with open(path, "rb") as fh:
        return fh.read(limit) if limit else fh.read()


def seed_pif_ram(pif, cic):
    pif[:]=b"\x00"*PIF_RAM_SIZE
    for i in range(4): pif[i*4]=0x01
    for i in range(4): pif[0x20+i*4]=pif[0x21+i*4]=pif[0x22+i*4]=pif[0x23+i*4]=0x00
    pif[0x18]=0x00; pif[0x19]=0x04
    cb = {CIC_NUS_6101:(0x00,0x06,0x3F,0x3F),CIC_NUS_7102:(0x00,0x06,0x3F,0x3F),CIC_NUS_6102:(0x00,0x02,0x3F,0x3F),CIC_NUS_6103:(0x00,0x02,0x78,0x3F),CIC_NUS_6105:(0x00,0x02,0x91,0x3F),CIC_NUS_6106:(0x00,0x02,0x85,0x3F)}
    if cic in cb: pif[36],pif[37],pif[38],pif[39]=cb[cic]

def cic_6105_response(challenge: List[int]) -> List[int]:
    """CIC-NUS-6105 challenge/response over 4-bit nibbles (X-Scale's algorithm)."""
    lut0 = (0x4, 0x7, 0xA, 0x7, 0xE, 0x5, 0xE, 0x1, 0xC, 0xF, 0x8, 0xF, 0x6, 0x3, 0x6, 0x9)
    lut1 = (0x4, 0x1, 0xA, 0x7, 0xE, 0x5, 0xE, 0x1, 0xC, 0x9, 0x8, 0x5, 0x6, 0x3, 0xC, 0x9)
    key, lut, out = 0xB, lut0, []
    for c in challenge:
        r = (key + 5 * c) & 0xF
        out.append(r)
        key = lut[r]
        sgn = (r >> 3) & 1
        mag = ((~r) if sgn else r) & 0x7
        mod = sgn if mag % 3 == 1 else 1 - sgn
        if lut is lut1 and r in (0x1, 0x9):
            mod = 1
        if lut is lut1 and r in (0xB, 0xE):
            mod = 0
        lut = lut1 if mod == 1 else lut0
    return out

def pak_address_crc(addr: int) -> int:
    """libultra __osContAddressCrc: 5-bit CRC over the 11-bit Controller Pak block address."""
    ret = 0
    bit = 0x400
    while bit:
        ret <<= 1
        if addr & bit:
            ret = ret ^ 0x14 if ret & 0x20 else ret + 1
        elif ret & 0x20:
            ret ^= 0x15
        bit >>= 1
    for _ in range(5):
        ret <<= 1
        if ret & 0x20:
            ret ^= 0x15
    return ret & 0x1F


def pak_data_crc(data) -> int:
    """libultra __osContDataCrc: CRC-8 (poly 0x85) over a 32-byte pak block."""
    ret = 0
    for byte in data[:32]:
        j = 0x80
        while j:
            ret <<= 1
            if byte & j:
                ret = ret ^ 0x84 if ret & 0x100 else ret + 1
            elif ret & 0x100:
                ret ^= 0x85
            j >>= 1
    for _ in range(8):
        ret <<= 1
        if ret & 0x100:
            ret ^= 0x85
    return ret & 0xFF


# Joybus pad accessory kinds per port.
PAK_NONE, PAK_MEMPAK, PAK_RUMBLE = "none", "mempak", "rumble"


def get_rom_region(rom):
    if len(rom)<0x3F: return REGION_NTSC
    if rom[0x3E] == 0x42: return REGION_MPAL  # Brazil
    return REGION_PAL if rom[0x3E] in (0x44,0x46,0x49,0x50,0x53,0x55,0x58,0x59) else REGION_NTSC

# Game database keyed by the 2-letter cart ID (header 0x3C). Only entries known with confidence;
# unknown IDs fall back to the heuristic table below. ram8 = needs the Expansion Pak;
# cf = counter factor (COUNT ticks per instruction, default 2) for timing-sensitive titles.
E4, E16, SR, FL, NONE = SAVE_EEPROM_4K, SAVE_EEPROM_16K, SAVE_SRAM, SAVE_FLASHRAM, SAVE_AUTO
GAME_DB: Dict[str, Dict[str, Any]] = {
    "SM": {"name": "Super Mario 64", "save": E4},
    "ZL": {"name": "The Legend of Zelda: Ocarina of Time", "save": SR},
    "ZS": {"name": "The Legend of Zelda: Majora's Mask", "save": FL, "ram8": True},
    "KT": {"name": "Mario Kart 64", "save": E4},
    "FX": {"name": "Star Fox 64", "save": E4},
    "AL": {"name": "Super Smash Bros.", "save": SR},
    "WR": {"name": "Wave Race 64", "save": E4},
    "PW": {"name": "Pilotwings 64", "save": E4},
    "YS": {"name": "Yoshi's Story", "save": E16},
    "FZ": {"name": "F-Zero X", "save": SR},
    "MQ": {"name": "Paper Mario", "save": FL},
    "GE": {"name": "GoldenEye 007", "save": E4},
    "PD": {"name": "Perfect Dark", "save": E16},
    "BK": {"name": "Banjo-Kazooie", "save": E4},
    "B7": {"name": "Banjo-Tooie", "save": E16},
    "DO": {"name": "Donkey Kong 64", "save": E16, "ram8": True},
    "FU": {"name": "Conker's Bad Fur Day", "save": E16},
    "DY": {"name": "Diddy Kong Racing", "save": E4},
    "MW": {"name": "Mario Party 2", "save": E4},
    "MV": {"name": "Mario Party 3", "save": E16},
    "M8": {"name": "Mario Tennis", "save": E16},
    "MF": {"name": "Mario Golf", "save": SR},
    "K4": {"name": "Kirby 64: The Crystal Shards", "save": SR},
    "PO": {"name": "Pokemon Stadium", "save": FL},
    "P3": {"name": "Pokemon Stadium 2", "save": FL},
    "YW": {"name": "Harvest Moon 64", "save": SR},
    "OB": {"name": "Ogre Battle 64", "save": SR},
    "RE": {"name": "Resident Evil 2", "save": SR},
    "BM": {"name": "Bomberman 64", "save": E4},
    "AF": {"name": "Animal Forest", "save": FL},
}
del E4, E16, SR, FL, NONE


def game_info(rom) -> Dict[str, Any]:
    if len(rom) < 0x40:
        return {}
    return GAME_DB.get(bytes(rom[0x3C:0x3E]).decode("ascii", "ignore").upper(), {})


def detect_save_type(rom):
    if len(rom) < 0x40: return SAVE_AUTO
    info = game_info(rom)
    if "save" in info:
        return info["save"]
    cart = rom[0x3C:0x3E].decode("ascii", "ignore").upper()
    # Commercial cart-ID → save media (UltraHLE skipped EEPROM; cathle HLE's it).
    eeprom4 = {
        "SM", "GE", "NE", "KT", "SV", "WR", "RC", "BM", "BE", "TW", "IR", "GU",
        "CL", "IC", "LB", "MW", "SI", "SQ", "TE", "TM", "VG", "VT", "WA",
    }
    eeprom16 = {"ZS", "DZ", "FU", "PG", "CZ", "DL", "DO", "JD"}
    sram = {"ZL", "TP", "YW", "NB", "MZ", "CF", "DK", "FZ", "KI", "OS", "PD", "WC", "YF"}
    flash = {"PO", "MX", "DQ", "PN", "CC", "CR", "DR", "ML", "RE", "YS"}
    if cart in flash: return SAVE_FLASHRAM
    if cart in sram: return SAVE_SRAM
    if cart in eeprom16: return SAVE_EEPROM_16K
    if cart in eeprom4: return SAVE_EEPROM_4K
    return SAVE_EEPROM_4K

class N64Header:
    __slots__=("pi_bsd_dom1_lat","pi_bsd_dom1_pwd","pi_bsd_dom1_pgs","pi_bsd_dom1_rls","clock_rate","boot_address","release","crc1","crc2","title","cart_id")
    def __init__(self,data):
        if len(data)>=0x40:
            self.pi_bsd_dom1_lat=data[0];self.pi_bsd_dom1_pwd=data[1];self.pi_bsd_dom1_pgs=data[2];self.pi_bsd_dom1_rls=data[3]
            self.clock_rate=be32(data,0x04);self.boot_address=be32(data,0x08);self.release=be32(data,0x0C)
            self.crc1=be32(data,0x10);self.crc2=be32(data,0x14)
            self.title=data[0x20:0x34].decode("ascii","ignore").strip("\x00").strip()
            self.cart_id=data[0x3C:0x3E].decode("ascii","ignore")
        else:
            self.clock_rate=0;self.boot_address=0x80000400;self.release=0;self.crc1=self.crc2=0;self.title="UNKNOWN";self.cart_id="??"

@dataclass
class TLBEntry: mask:int=0;vpn2:int=0;g:bool=False;asid:int=0;pfn0:int=0;c0:int=0;d0:bool=False;v0:bool=False;pfn1:int=0;c1:int=0;d1:bool=False;v1:bool=False

_lwl_mask=[0,0xFF,0xFFFF,0xFFFFFF];_lwl_shift=[0,8,16,24]
_lwr_mask=[0xFFFFFF00,0xFFFF0000,0xFF000000,0];_lwr_shift=[24,16,8,0]
_swl_mask=[0,0xFF000000,0xFFFF0000,0xFFFFFF00];_swl_shift=[0,8,16,24]
_swr_mask=[0x00FFFFFF,0x0000FFFF,0x000000FF,0x00000000];_swr_shift=[24,16,8,0]
_ldl_mask=[0,0xFF,0xFFFF,0xFFFFFF,0xFFFFFFFF,0xFFFFFFFFFF,0xFFFFFFFFFFFF,0xFFFFFFFFFFFFFF];_ldl_shift=[0,8,16,24,32,40,48,56]
_ldr_mask=[0xFFFFFFFFFFFFFF00,0xFFFFFFFFFFFF0000,0xFFFFFFFFFF000000,0xFFFFFFFF00000000,0xFFFFFF0000000000,0xFFFF000000000000,0xFF00000000000000,0];_ldr_shift=[56,48,40,32,24,16,8,0]
_sdl_mask=[0,0xFF00000000000000,0xFFFF000000000000,0xFFFFFF0000000000,0xFFFFFFFF00000000,0xFFFFFFFFFF000000,0xFFFFFFFFFFFF0000,0xFFFFFFFFFFFFFF00];_sdl_shift=[0,8,16,24,32,40,48,56]
_sdr_mask=[0x00FFFFFFFFFFFFFF,0x0000FFFFFFFFFFFF,0x000000FFFFFFFFFF,0x00000000FFFFFFFF,0x0000000000FFFFFF,0x000000000000FFFF,0x00000000000000FF,0x0000000000000000];_sdr_shift=[56,48,40,32,24,16,8,0]
_ID_SPECIAL=0x00000;_ID_REGIMM=0x10000;_ID_COP0_RS=0x20000;_ID_COP0_CO=0x30000;_ID_COP1_RS=0x40000;_ID_COP1_BC=0x50000;_ID_FPU=0x60000;_ID_PRIMARY=0x70000
_ID_FPU_S=0;_ID_FPU_D=1;_ID_FPU_W=2;_ID_FPU_L=3;_FPU_FMT_MAP={0x10:_ID_FPU_S,0x11:_ID_FPU_D,0x14:_ID_FPU_W,0x15:_ID_FPU_L}
_DISPATCH:List[Optional[Callable]] = [None] * ((_ID_PRIMARY | 0x3F) + 1)
_OPCODE_CACHE: Dict[int, "N64Opcode"] = {}
_OPCODE_CACHE_MAX = 8192
OP_FORMAT_R="R";OP_FORMAT_I="I";OP_FORMAT_J="J";OP_FORMAT_CP="CP";OP_FORMAT_CP0_CO="CP0_CO";OP_FORMAT_REGIMM="REGIMM";OP_FORMAT_FPU_S="FPU_S";OP_FORMAT_FPU_D="FPU_D";OP_FORMAT_FPU_W="FPU_W";OP_FORMAT_FPU_L="FPU_L";OP_FORMAT_BC="BC";OP_FORMAT_BC1="BC1";OP_FORMAT_FPU_FMT="FPU_FMT"
PRIMARY_OPS={0x00:("SPECIAL",OP_FORMAT_R),0x01:("REGIMM",OP_FORMAT_REGIMM),0x02:("J",OP_FORMAT_J),0x03:("JAL",OP_FORMAT_J),0x04:("BEQ",OP_FORMAT_I),0x05:("BNE",OP_FORMAT_I),0x06:("BLEZ",OP_FORMAT_I),0x07:("BGTZ",OP_FORMAT_I),0x08:("ADDI",OP_FORMAT_I),0x09:("ADDIU",OP_FORMAT_I),0x0A:("SLTI",OP_FORMAT_I),0x0B:("SLTIU",OP_FORMAT_I),0x0C:("ANDI",OP_FORMAT_I),0x0D:("ORI",OP_FORMAT_I),0x0E:("XORI",OP_FORMAT_I),0x0F:("LUI",OP_FORMAT_I),0x10:("COP0",OP_FORMAT_CP),0x11:("COP1",OP_FORMAT_CP),0x12:("COP2",OP_FORMAT_CP),0x13:("COP3",OP_FORMAT_CP),0x14:("BEQL",OP_FORMAT_I),0x15:("BNEL",OP_FORMAT_I),0x16:("BLEZL",OP_FORMAT_I),0x17:("BGTZL",OP_FORMAT_I),0x18:("DADDI",OP_FORMAT_I),0x19:("DADDIU",OP_FORMAT_I),0x1A:("LDL",OP_FORMAT_I),0x1B:("LDR",OP_FORMAT_I),0x1C:("PATCH",OP_FORMAT_I),0x1D:("GROUP",OP_FORMAT_I),0x1E:("RESERVED_1E",None),0x1F:("RESERVED_1F",None),0x20:("LB",OP_FORMAT_I),0x21:("LH",OP_FORMAT_I),0x22:("LWL",OP_FORMAT_I),0x23:("LW",OP_FORMAT_I),0x24:("LBU",OP_FORMAT_I),0x25:("LHU",OP_FORMAT_I),0x26:("LWR",OP_FORMAT_I),0x27:("LWU",OP_FORMAT_I),0x28:("SB",OP_FORMAT_I),0x29:("SH",OP_FORMAT_I),0x2A:("SWL",OP_FORMAT_I),0x2B:("SW",OP_FORMAT_I),0x2C:("SDL",OP_FORMAT_I),0x2D:("SDR",OP_FORMAT_I),0x2E:("SWR",OP_FORMAT_I),0x2F:("CACHE",OP_FORMAT_I),0x30:("LL",OP_FORMAT_I),0x31:("LWC1",OP_FORMAT_I),0x32:("LWC2",OP_FORMAT_I),0x33:("LWC3",OP_FORMAT_I),0x34:("LLD",OP_FORMAT_I),0x35:("LDC1",OP_FORMAT_I),0x36:("LDC2",OP_FORMAT_I),0x37:("LD",OP_FORMAT_I),0x38:("SC",OP_FORMAT_I),0x39:("SWC1",OP_FORMAT_I),0x3A:("SWC2",OP_FORMAT_I),0x3B:("SWC3",OP_FORMAT_I),0x3C:("SCD",OP_FORMAT_I),0x3D:("SDC1",OP_FORMAT_I),0x3E:("SDC2",OP_FORMAT_I),0x3F:("SD",OP_FORMAT_I)}
SPECIAL_OPS={0x00:("SLL",OP_FORMAT_R),0x01:("RESERVED_SLL_01",None),0x02:("SRL",OP_FORMAT_R),0x03:("SRA",OP_FORMAT_R),0x04:("SLLV",OP_FORMAT_R),0x05:("RESERVED_SLLV_05",None),0x06:("SRLV",OP_FORMAT_R),0x07:("SRAV",OP_FORMAT_R),0x08:("JR",OP_FORMAT_R),0x09:("JALR",OP_FORMAT_R),0x0A:("MOVZ",OP_FORMAT_R),0x0B:("MOVN",OP_FORMAT_R),0x0C:("SYSCALL",OP_FORMAT_R),0x0D:("BREAK",OP_FORMAT_R),0x0E:("RESERVED_SP_0E",None),0x0F:("SYNC",OP_FORMAT_R),0x10:("MFHI",OP_FORMAT_R),0x11:("MTHI",OP_FORMAT_R),0x12:("MFLO",OP_FORMAT_R),0x13:("MTLO",OP_FORMAT_R),0x14:("DSLLV",OP_FORMAT_R),0x15:("RESERVED_DSLLV_15",None),0x16:("DSRLV",OP_FORMAT_R),0x17:("DSRAV",OP_FORMAT_R),0x18:("MULT",OP_FORMAT_R),0x19:("MULTU",OP_FORMAT_R),0x1A:("DIV",OP_FORMAT_R),0x1B:("DIVU",OP_FORMAT_R),0x1C:("DMULT",OP_FORMAT_R),0x1D:("DMULTU",OP_FORMAT_R),0x1E:("DDIV",OP_FORMAT_R),0x1F:("DDIVU",OP_FORMAT_R),0x20:("ADD",OP_FORMAT_R),0x21:("ADDU",OP_FORMAT_R),0x22:("SUB",OP_FORMAT_R),0x23:("SUBU",OP_FORMAT_R),0x24:("AND",OP_FORMAT_R),0x25:("OR",OP_FORMAT_R),0x26:("XOR",OP_FORMAT_R),0x27:("NOR",OP_FORMAT_R),0x28:("RESERVED_SP_28",None),0x29:("RESERVED_SP_29",None),0x2A:("SLT",OP_FORMAT_R),0x2B:("SLTU",OP_FORMAT_R),0x2C:("DADD",OP_FORMAT_R),0x2D:("DADDU",OP_FORMAT_R),0x2E:("DSUB",OP_FORMAT_R),0x2F:("DSUBU",OP_FORMAT_R),0x30:("TGE",OP_FORMAT_R),0x31:("TGEU",OP_FORMAT_R),0x32:("TLT",OP_FORMAT_R),0x33:("TLTU",OP_FORMAT_R),0x34:("TEQ",OP_FORMAT_R),0x35:("RESERVED_SP_35",None),0x36:("TNE",OP_FORMAT_R),0x37:("RESERVED_SP_37",None),0x38:("DSLL",OP_FORMAT_R),0x39:("RESERVED_DSLL_39",None),0x3A:("DSRL",OP_FORMAT_R),0x3B:("DSRA",OP_FORMAT_R),0x3C:("DSLL32",OP_FORMAT_R),0x3D:("RESERVED_DSLL32_3D",None),0x3E:("DSRL32",OP_FORMAT_R),0x3F:("DSRA32",OP_FORMAT_R)}
REGIMM_OPS={0x00:("BLTZ",OP_FORMAT_I),0x01:("BGEZ",OP_FORMAT_I),0x02:("BLTZL",OP_FORMAT_I),0x03:("BGEZL",OP_FORMAT_I),0x04:("RESERVED_RI_04",None),0x05:("RESERVED_RI_05",None),0x06:("RESERVED_RI_06",None),0x07:("RESERVED_RI_07",None),0x08:("TGEI",OP_FORMAT_I),0x09:("TGEIU",OP_FORMAT_I),0x0A:("TLTI",OP_FORMAT_I),0x0B:("TLTIU",OP_FORMAT_I),0x0C:("TEQI",OP_FORMAT_I),0x0D:("RESERVED_RI_0D",None),0x0E:("TNEI",OP_FORMAT_I),0x0F:("RESERVED_RI_0F",None),0x10:("BLTZAL",OP_FORMAT_I),0x11:("BGEZAL",OP_FORMAT_I),0x12:("BLTZALL",OP_FORMAT_I),0x13:("BGEZALL",OP_FORMAT_I)}
COP0_RS={0x00:("MFC0",OP_FORMAT_CP),0x01:("DMFC0",OP_FORMAT_CP),0x02:("CFC0",OP_FORMAT_CP),0x03:("RESERVED_C0_RS_03",None),0x04:("MTC0",OP_FORMAT_CP),0x05:("DMTC0",OP_FORMAT_CP),0x06:("CTC0",OP_FORMAT_CP),0x07:("RESERVED_C0_RS_07",None),0x08:("BC0",OP_FORMAT_BC),0x09:("RESERVED_C0_RS_09",None),0x0A:("RESERVED_C0_RS_0A",None),0x0B:("RESERVED_C0_RS_0B",None),0x0C:("RESERVED_C0_RS_0C",None),0x0D:("RESERVED_C0_RS_0D",None),0x0E:("RESERVED_C0_RS_0E",None),0x0F:("RESERVED_C0_RS_0F",None),0x10:("COP0_CO",OP_FORMAT_CP0_CO)}
COP0_CO={0x00:("RESERVED_C0_CO_00",None),0x01:("TLBR",OP_FORMAT_CP0_CO),0x02:("TLBWI",OP_FORMAT_CP0_CO),0x03:("RESERVED_C0_CO_03",None),0x04:("RESERVED_C0_CO_04",None),0x05:("RESERVED_C0_CO_05",None),0x06:("TLBWR",OP_FORMAT_CP0_CO),0x07:("RESERVED_C0_CO_07",None),0x08:("TLBP",OP_FORMAT_CP0_CO),0x18:("ERET",OP_FORMAT_CP0_CO),0x20:("WAIT",OP_FORMAT_CP0_CO)}
COP1_RS={0x00:("MFC1",OP_FORMAT_CP),0x01:("DMFC1",OP_FORMAT_CP),0x02:("CFC1",OP_FORMAT_CP),0x03:("RESERVED_C1_RS_03",None),0x04:("MTC1",OP_FORMAT_CP),0x05:("DMTC1",OP_FORMAT_CP),0x06:("CTC1",OP_FORMAT_CP),0x07:("RESERVED_C1_RS_07",None),0x08:("BC1",OP_FORMAT_BC1),0x10:("S",OP_FORMAT_FPU_S),0x11:("D",OP_FORMAT_FPU_D),0x14:("W",OP_FORMAT_FPU_W),0x15:("L",OP_FORMAT_FPU_L)}
COP1_FUNCT={0x00:("ADD",OP_FORMAT_FPU_FMT),0x01:("SUB",OP_FORMAT_FPU_FMT),0x02:("MUL",OP_FORMAT_FPU_FMT),0x03:("DIV",OP_FORMAT_FPU_FMT),0x04:("SQRT",OP_FORMAT_FPU_FMT),0x05:("ABS",OP_FORMAT_FPU_FMT),0x06:("MOV",OP_FORMAT_FPU_FMT),0x07:("NEG",OP_FORMAT_FPU_FMT),0x08:("ROUND.L",OP_FORMAT_FPU_FMT),0x09:("TRUNC.L",OP_FORMAT_FPU_FMT),0x0A:("CEIL.L",OP_FORMAT_FPU_FMT),0x0B:("FLOOR.L",OP_FORMAT_FPU_FMT),0x0C:("ROUND.W",OP_FORMAT_FPU_FMT),0x0D:("TRUNC.W",OP_FORMAT_FPU_FMT),0x0E:("CEIL.W",OP_FORMAT_FPU_FMT),0x0F:("FLOOR.W",OP_FORMAT_FPU_FMT),0x15:("RECIP",OP_FORMAT_FPU_FMT),0x16:("RSQRT",OP_FORMAT_FPU_FMT),0x20:("CVT.S",OP_FORMAT_FPU_FMT),0x21:("CVT.D",OP_FORMAT_FPU_FMT),0x24:("CVT.W",OP_FORMAT_FPU_FMT),0x25:("CVT.L",OP_FORMAT_FPU_FMT),0x30:("C.F",OP_FORMAT_FPU_FMT),0x31:("C.UN",OP_FORMAT_FPU_FMT),0x32:("C.EQ",OP_FORMAT_FPU_FMT),0x33:("C.UEQ",OP_FORMAT_FPU_FMT),0x34:("C.OLT",OP_FORMAT_FPU_FMT),0x35:("C.ULT",OP_FORMAT_FPU_FMT),0x36:("C.OLE",OP_FORMAT_FPU_FMT),0x37:("C.ULE",OP_FORMAT_FPU_FMT),0x38:("C.SF",OP_FORMAT_FPU_FMT),0x39:("C.NGLE",OP_FORMAT_FPU_FMT),0x3A:("C.SEQ",OP_FORMAT_FPU_FMT),0x3B:("C.NGL",OP_FORMAT_FPU_FMT),0x3C:("C.LT",OP_FORMAT_FPU_FMT),0x3D:("C.NGE",OP_FORMAT_FPU_FMT),0x3E:("C.LE",OP_FORMAT_FPU_FMT),0x3F:("C.NGT",OP_FORMAT_FPU_FMT)}

@dataclass
class CheatCode: name:str="";code:str="";enabled:bool=True
class CheatEngine:
    def __init__(self): self.codes:List[CheatCode]=[]; self.active:List[CheatCode]=[]
    def add(self,name,code): cc=CheatCode(name=name,code=code,enabled=True); self.codes.append(cc); self.active.append(cc)
    def toggle(self,idx):
        if 0<=idx<len(self.codes): self.codes[idx].enabled=not self.codes[idx].enabled; self.active=[c for c in self.codes if c.enabled]
    def apply(self,bus,rdram):
        for cc in self.active:
            if not cc.code.strip(): continue
            try:
                parts=cc.code.strip().split()
                if len(parts)>=2 and len(parts[0])==8 and len(parts[1])==8:
                    addr=int(parts[0],16);val=int(parts[1],16);ct=(addr>>28)&0xF;aa=(addr&0x0FFFFFFF)&0x00FFFFFF
                    if ct==0 and aa<RDRAM_SIZE-3: put_be32(rdram,aa,val)
                    elif ct==1 and aa<RDRAM_SIZE-1: struct.pack_into(">H",rdram,aa,val&MASK_16)
            except: pass

# libultra EEPROM_TYPE_* returned by osEepromProbe
EEPROM_TYPE_4K = 0x8000
EEPROM_TYPE_16K = 0xC000
EEPROM_BLOCK = 8


class SaveManager:
    def __init__(self):
        self.save_type=SAVE_AUTO; self.eeprom=bytearray(EEPROM_16K_SIZE); self.sram=bytearray(SRAM_SIZE)
        self.flashram=bytearray(b"\xFF" * FLASHRAM_SIZE); self.flashram_mode=0; self.flashram_addr=0; self.dirty=False
        self._flash_status_init()
    def reset(self):
        self.eeprom=bytearray(EEPROM_16K_SIZE); self.sram=bytearray(SRAM_SIZE); self.flashram=bytearray(b"\xFF" * FLASHRAM_SIZE)
        self.flashram_mode=0; self.flashram_addr=0; self.dirty=False
        self._flash_status_init()
    def get_save_size(self): return {SAVE_EEPROM_4K:EEPROM_4K_SIZE,SAVE_EEPROM_16K:EEPROM_16K_SIZE,SAVE_SRAM:SRAM_SIZE,SAVE_FLASHRAM:FLASHRAM_SIZE}.get(self.save_type,0)
    def eeprom_present(self) -> bool:
        return self.save_type in (SAVE_AUTO, SAVE_EEPROM_4K, SAVE_EEPROM_16K)
    def eeprom_capacity(self) -> int:
        if self.save_type == SAVE_EEPROM_16K:
            return EEPROM_16K_SIZE
        if self.save_type in (SAVE_EEPROM_4K, SAVE_AUTO):
            return EEPROM_4K_SIZE
        return 0
    def eeprom_probe(self) -> int:
        if not self.eeprom_present():
            return 0
        return EEPROM_TYPE_16K if self.save_type == SAVE_EEPROM_16K else EEPROM_TYPE_4K
    def eeprom_read_block(self, block: int, out: bytearray, off: int = 0) -> int:
        cap = self.eeprom_capacity()
        if cap <= 0:
            return -1
        addr = int(block) * EEPROM_BLOCK
        if addr < 0 or addr + EEPROM_BLOCK > cap:
            return -1
        out[off:off + EEPROM_BLOCK] = self.eeprom[addr:addr + EEPROM_BLOCK]
        return 0
    def eeprom_write_block(self, block: int, data, off: int = 0) -> int:
        cap = self.eeprom_capacity()
        if cap <= 0:
            return -1
        addr = int(block) * EEPROM_BLOCK
        if addr < 0 or addr + EEPROM_BLOCK > cap:
            return -1
        self.eeprom[addr:addr + EEPROM_BLOCK] = bytes(data[off:off + EEPROM_BLOCK])
        self.dirty = True
        return 0
    def eeprom_long_read(self, block: int, nbytes: int, bus, vaddr: int) -> int:
        if nbytes <= 0 or (nbytes & 7):
            return -1
        nblocks = nbytes // EEPROM_BLOCK
        tmp = bytearray(EEPROM_BLOCK)
        for i in range(nblocks):
            if self.eeprom_read_block(block + i, tmp) != 0:
                return -1
            for b in range(EEPROM_BLOCK):
                bus.write_u8(u32(vaddr + i * EEPROM_BLOCK + b), tmp[b])
        return 0
    def eeprom_long_write(self, block: int, nbytes: int, bus, vaddr: int) -> int:
        if nbytes <= 0 or (nbytes & 7):
            return -1
        nblocks = nbytes // EEPROM_BLOCK
        tmp = bytearray(EEPROM_BLOCK)
        for i in range(nblocks):
            for b in range(EEPROM_BLOCK):
                tmp[b] = bus.read_u8(u32(vaddr + i * EEPROM_BLOCK + b)) & 0xFF
            if self.eeprom_write_block(block + i, tmp) != 0:
                return -1
        return 0
    # ── Cartridge domain 2 (0x08000000): SRAM or FlashRAM ──
    # FlashRAM (MX29L1100 / MN63F81): commands written to 0x08010000, status read at 0x08000000.
    FLASH_IDLE, FLASH_READ, FLASH_STATUS, FLASH_ERASE, FLASH_WRITE = 0, 1, 2, 3, 4

    def _flash_status_init(self):
        self.flash_status = 0x1111800100C20000   # silicon ID (Macronix, 1 Mbit)
        self.flash_page = bytearray(128)
        self.flash_offset = 0
        self.flash_chip_erase = False

    def flash_command(self, cmd: int):
        op = (cmd >> 24) & 0xFF
        if op == 0x4B:      # sector erase: 16 KB sector containing page
            self.flashram_mode = self.FLASH_ERASE; self.flash_chip_erase = False
            self.flash_offset = (cmd & 0xFFFF) * 128
            self.flash_status = 0x1111800800C20000
        elif op == 0x3C:    # chip erase prepare
            self.flashram_mode = self.FLASH_ERASE; self.flash_chip_erase = True
            self.flash_status = 0x1111800800C20000
        elif op == 0x78:    # erase mode (status)
            self.flashram_mode = self.FLASH_ERASE
            self.flash_status = 0x1111800800C20000
        elif op == 0xA5:    # set write page
            self.flash_offset = (cmd & 0xFFFF) * 128
            self.flash_status = 0x1111800400C20000
        elif op == 0xB4:    # write mode: next PI write fills the 128-byte page buffer
            self.flashram_mode = self.FLASH_WRITE
        elif op == 0xD2:    # execute
            if self.flashram_mode == self.FLASH_ERASE:
                if self.flash_chip_erase:
                    self.flashram[:] = b"\xFF" * FLASHRAM_SIZE
                else:
                    base = self.flash_offset & ~0x3FFF & (FLASHRAM_SIZE - 1)
                    self.flashram[base:base + 0x4000] = b"\xFF" * 0x4000
                self.dirty = True
            elif self.flashram_mode == self.FLASH_WRITE:
                o = self.flash_offset & (FLASHRAM_SIZE - 1)
                self.flashram[o:o + 128] = self.flash_page
                self.dirty = True
        elif op == 0xE1:    # status mode
            self.flashram_mode = self.FLASH_STATUS
            self.flash_status = 0x1111800100C20000
        elif op == 0xF0:    # read array mode
            self.flashram_mode = self.FLASH_READ
            self.flash_status = 0x11118004F0000000
        else:
            return False
        return True

    def cart2_read32(self, off: int) -> int:
        """CPU load from domain 2 (offset from 0x08000000)."""
        if self.save_type == SAVE_FLASHRAM:
            return (self.flash_status >> 32) & MASK_32
        if self.save_type == SAVE_SRAM and off + 4 <= len(self.sram):
            return be32(self.sram, off)
        return 0

    def cart2_write32(self, off: int, val: int):
        if self.save_type == SAVE_FLASHRAM:
            if off >= 0x10000:
                self.flash_command(val)
        elif self.save_type == SAVE_SRAM and off + 4 <= len(self.sram):
            put_be32(self.sram, off, val); self.dirty = True

    def pi_read(self, ca, ln, rdram, da):
        """Cart → RDRAM DMA from domain 2 (ca = full cart address)."""
        off = (ca - 0x08000000) & 0x07FFFFFF
        ln = max(0, min(ln, len(rdram) - da))
        if self.save_type == SAVE_SRAM:
            o = off & 0x3FFFF
            src = self.sram[o:o + ln]
            rdram[da:da + len(src)] = src
        elif self.save_type == SAVE_FLASHRAM:
            if self.flashram_mode == self.FLASH_READ:
                o = (off * 2) & (FLASHRAM_SIZE - 1)   # array reads use 16-bit word addressing
                src = self.flashram[o:o + ln]
                rdram[da:da + len(src)] = src
            else:
                st = struct.pack(">Q", self.flash_status)
                rdram[da:da + min(ln, 8)] = st[:min(ln, 8)]

    def pi_write(self, ca, ln, rdram, da):
        """RDRAM → cart DMA into domain 2."""
        off = (ca - 0x08000000) & 0x07FFFFFF
        if self.save_type == SAVE_SRAM:
            o = off & 0x3FFFF
            ln = max(0, min(ln, len(self.sram) - o))
            self.sram[o:o + ln] = rdram[da:da + ln]
            self.dirty = True
        elif self.save_type == SAVE_FLASHRAM and self.flashram_mode == self.FLASH_WRITE:
            self.flash_page[:] = bytes(rdram[da:da + 128]).ljust(128, b"\xFF")

    # ── persistence ──
    def _files(self, base: str):
        return {"eep": base + ".eep", "sra": base + ".sra", "fla": base + ".fla"}

    def load_files(self, base: str):
        f = self._files(base)
        def rd(path, buf):
            try:
                with open(path, "rb") as fh:
                    data = fh.read(len(buf))
                buf[:len(data)] = data
            except OSError:
                pass
        rd(f["eep"], self.eeprom); rd(f["sra"], self.sram); rd(f["fla"], self.flashram)
        self.dirty = False

    def save_files(self, base: str) -> bool:
        """Write only the save media this cart uses. Returns True if anything was written."""
        f = self._files(base)
        os.makedirs(os.path.dirname(base) or ".", exist_ok=True)
        if self.save_type in (SAVE_EEPROM_4K, SAVE_EEPROM_16K, SAVE_AUTO):
            data, path = self.eeprom[:self.eeprom_capacity()], f["eep"]
        elif self.save_type == SAVE_SRAM:
            data, path = self.sram, f["sra"]
        elif self.save_type == SAVE_FLASHRAM:
            data, path = self.flashram, f["fla"]
        else:
            return False
        tmp = path + ".tmp"
        with open(tmp, "wb") as fh:
            fh.write(bytes(data))
        os.replace(tmp, path)
        self.dirty = False
        return True


# RGB5551 → R/G/B expansion LUTs (built once).
# 5-bit → 8-bit with bit replication so full intensity is 255.
_RGB555_R = bytearray(((((px >> 11) & 0x1F) << 3) | (((px >> 11) & 0x1F) >> 2)) for px in range(65536))
_RGB555_G = bytearray(((((px >> 6) & 0x1F) << 3) | (((px >> 6) & 0x1F) >> 2)) for px in range(65536))
_RGB555_B = bytearray(((((px >> 1) & 0x1F) << 3) | (((px >> 1) & 0x1F) >> 2)) for px in range(65536))


def rdram_rgb5551_to_ppm(rdram, origin, width, height, scale: int = 1):
    """Convert RGB5551 RDRAM to binary PPM. ``scale`` 2 ≈ 4× faster (160×120)."""
    origin &= 0xFFFFFF
    width = 320 if width < 16 or width > 640 else int(width)
    height = 240 if height < 1 or height > 240 else min(int(height), 240)
    scale = 2 if scale >= 2 else 1
    out_w = width // scale
    out_h = height // scale
    stride = width * 2
    need = origin + stride * height
    if origin < 0 or need > len(rdram):
        return None
    hdr = f"P6\n{out_w} {out_h}\n255\n".encode("ascii")
    out = bytearray(out_w * out_h * 3)
    mv = memoryview(rdram)
    lr, lg, lb = _RGB555_R, _RGB555_G, _RGB555_B
    o = 0
    y_step = scale
    x_step = scale * 2
    for y in range(0, height, y_step):
        row = origin + y * stride
        x = 0
        while x < stride:
            px = (mv[row + x] << 8) | mv[row + x + 1]
            out[o] = lr[px]
            out[o + 1] = lg[px]
            out[o + 2] = lb[px]
            o += 3
            x += x_step
    return hdr + out


try:
    import numpy as _np  # optional acceleration
except Exception:  # pragma: no cover - numpy absent
    _np = None
USE_NUMPY = _np is not None


def vi_frame_to_ppm(rdram, origin: int, stride: int, w: int, h: int, bpp: int, use_numpy: Optional[bool] = None) -> Optional[bytes]:
    """Scan out a w×h window of an RDRAM framebuffer (stride in pixels, 16- or 32-bit) to PPM."""
    origin &= 0xFFFFFF
    if w <= 0 or h <= 0 or stride <= 0:
        return None
    need = origin + (stride * (h - 1) + w) * bpp
    if need > len(rdram):
        h = max(0, (len(rdram) - origin) // (stride * bpp))
        if h <= 0:
            return None
    hdr = f"P6\n{w} {h}\n255\n".encode("ascii")
    if use_numpy is None:
        use_numpy = USE_NUMPY
    if use_numpy and _np is not None:
        if bpp == 2:
            a = _np.frombuffer(rdram, dtype=">u2", count=stride * h, offset=origin).reshape(h, stride)[:, :w].astype(_np.uint32)
            r = (a >> 11) & 31; g = (a >> 6) & 31; b = (a >> 1) & 31
            rgb = _np.stack(((r << 3) | (r >> 2), (g << 3) | (g >> 2), (b << 3) | (b >> 2)), axis=-1).astype(_np.uint8)
        else:
            a = _np.frombuffer(rdram, dtype=_np.uint8, count=stride * h * 4, offset=origin).reshape(h, stride, 4)[:, :w, :3]
            rgb = _np.ascontiguousarray(a)
        return hdr + rgb.tobytes()
    out = bytearray(w * h * 3)
    o = 0
    if bpp == 2:
        lr, lg, lb = _RGB555_R, _RGB555_G, _RGB555_B
        for y in range(h):
            row = origin + y * stride * 2
            for x in range(row, row + w * 2, 2):
                px = (rdram[x] << 8) | rdram[x + 1]
                out[o] = lr[px]; out[o + 1] = lg[px]; out[o + 2] = lb[px]
                o += 3
    else:
        for y in range(h):
            row = origin + y * stride * 4
            for x in range(row, row + w * 4, 4):
                out[o] = rdram[x]; out[o + 1] = rdram[x + 1]; out[o + 2] = rdram[x + 2]
                o += 3
    return hdr + bytes(out)


def ppm_brightness(ppm: Optional[bytes]) -> float:
    """Mean channel value of a binary PPM body (0..255)."""
    if not ppm:
        return 0.0
    # Skip P6 header (3 lines).
    p = 0
    for _ in range(3):
        n = ppm.find(b"\n", p)
        if n < 0:
            return 0.0
        p = n + 1
    n = len(ppm) - p
    if n <= 0:
        return 0.0
    if USE_NUMPY and _np is not None:
        return int(_np.frombuffer(ppm, dtype=_np.uint8, offset=p).sum(dtype=_np.int64)) / n
    return sum(memoryview(ppm)[p:]) / n

def normalize_commercial_entry(addr):
    addr=u32(addr)
    if addr==0 or addr==MASK_32: return 0x80000400
    hi=addr>>24
    if hi in (0x80,0xA0,0xB0):
        if hi==0xB0: return 0x80000000|(addr&0x1FFFFFFF)
        return addr
    if addr<RDRAM_SIZE: return 0x80000000|addr
    if hi==0 and addr<0x04000000: return 0x80000000|addr
    return addr

def default_rom_directory():
    try: os.makedirs(_DEFAULT_ROM_DIR,exist_ok=True); return _DEFAULT_ROM_DIR
    except OSError: return _SCRIPT_DIR

R4300_CP0_REG_NAMES={0:"Index",1:"Random",2:"EntryLo0",3:"EntryLo1",4:"Context",5:"PageMask",6:"Wired",7:"Reserved_7",8:"BadVAddr",9:"Count",10:"EntryHi",11:"Compare",12:"Status",13:"Cause",14:"EPC",15:"PRId",16:"Config",17:"LLAddr",30:"ErrorEPC"}

class N64Opcode:
    __slots__=("word","op","rs","rt","rd","sa","funct","imm","simm","target","instr_id")
    def __init__(self,word):
        self.word=word&MASK_32; self.op=(self.word>>26)&0x3F; self.rs=(self.word>>21)&0x1F; self.rt=(self.word>>16)&0x1F
        self.rd=(self.word>>11)&0x1F; self.sa=(self.word>>6)&0x1F; self.funct=self.word&0x3F; self.imm=self.word&MASK_16; self.simm=sign16(self.imm); self.target=self.word&0x03FFFFFF
        if self.op==0: self.instr_id=_ID_SPECIAL|self.funct
        elif self.op==1: self.instr_id=_ID_REGIMM|self.rt
        elif self.op==0x10:
            if self.rs==0x10: self.instr_id=_ID_COP0_CO|self.funct
            else: self.instr_id=_ID_COP0_RS|self.rs
        elif self.op==0x11:
            if self.rs in _FPU_FMT_MAP: self.instr_id=_ID_FPU|(_FPU_FMT_MAP[self.rs]<<6)|self.funct
            elif self.rs==0x08: self.instr_id=_ID_COP1_BC|self.rt
            else: self.instr_id=_ID_COP1_RS|self.rs
        else: self.instr_id=_ID_PRIMARY|self.op
    def target_addr(self,pc): return u32(((pc+4)&0xF0000000)|(self.target<<2))
    def branch_addr(self,pc): return u32(pc+4+(self.simm<<2))


def get_opcode(word: int) -> N64Opcode:
    """Cached decode — tight boot/delay loops re-hit the same words constantly."""
    word &= MASK_32
    o = _OPCODE_CACHE.get(word)
    if o is not None:
        return o
    o = N64Opcode(word)
    if len(_OPCODE_CACHE) < _OPCODE_CACHE_MAX:
        _OPCODE_CACHE[word] = o
    return o


class TLBException(Exception):
    """Raised by DeviceBus.v_to_p in strict-TLB mode; turned into a CPU exception."""
    def __init__(self, code: int, vaddr: int, refill: bool):
        self.code = code; self.vaddr = vaddr; self.refill = refill


# ── DeviceBus with N64 register MMIO ──
class DeviceBus:
    def __init__(self, core):
        self.core = core
        self.regs = {}
        self.hw_interrupts = 0
        self.mi_intr_mask = 0
        self.mi_mode = 0
        self.mi_version = 0x02020102
        self.sp_status = SP_STATUS_HALT
        self.dpc_status = 0
        self.dps_regs = {}
        self.vi_field_serration = 0
        self.half_line = 0
        self.sp_dma_busy = False
        # Strict TLB: misses raise TLB exceptions (accurate mode). Off = legacy identity fallback.
        self.strict_tlb = False
        self.tlb_cache: Dict[int, Tuple[int, bool]] = {}
        self.reset()

    def reset(self):
        self.regs.clear()
        self.hw_interrupts = 0
        self.mi_intr_mask = 0
        self.mi_mode = 0
        self.sp_status = SP_STATUS_HALT
        self.dpc_status = 0
        self.dps_regs.clear()
        self.vi_field_serration = 0
        self.half_line = 0
        self.sp_dma_busy = False
        self.regs[VI_ORIGIN] = 0
        self.regs[VI_WIDTH] = 320
        self.regs[VI_V_CURRENT] = 0x3FF
        self.regs[VI_INTR] = 0x3FF
        self.core._vi_origin_set = False

    def v_to_p(self, addr, write=False):
        addr &= MASK_32
        # KSEG0/KSEG1 fast path (most game code + RDRAM mirrors).
        if 0x80000000 <= addr < 0xC0000000:
            return addr & 0x1FFFFFFF
        if self.strict_tlb:
            return self._tlb_translate(addr, write)
        tlb = self.core.cpu.tlb
        asid = self.core.cpu.cp0[CP0_ENTRYHI] & 0xFF
        vpn2 = (addr >> 13) & 0x7FFFF
        for entry in tlb:
            if entry.mask:
                extra = ((entry.mask >> 12) & 1) | ((entry.mask >> 13) & 1)
                if extra:
                    ms = 13 - extra
                    vpn2_m = (addr >> ms) & (0x7FFFF >> extra)
                    ev = entry.vpn2 >> extra
                    if ev == vpn2_m and (entry.g or entry.asid == asid):
                        eo = (addr >> (12 + extra)) & 1
                        offset_mask = (1 << (12 + extra)) - 1
                        if eo == 0 and entry.v0:
                            return ((entry.pfn0 >> extra) << (12 + extra)) | (addr & offset_mask)
                        if eo == 1 and entry.v1:
                            return ((entry.pfn1 >> extra) << (12 + extra)) | (addr & offset_mask)
            elif entry.vpn2 == vpn2 and (entry.g or entry.asid == asid):
                eo = (addr >> 12) & 1
                if eo == 0 and entry.v0:
                    return (entry.pfn0 << 12) | (addr & 0xFFF)
                if eo == 1 and entry.v1:
                    return (entry.pfn1 << 12) | (addr & 0xFFF)
        return addr & 0x1FFFFFFF

    def _tlb_translate(self, addr, write):
        """VR4300 TLB lookup with a 4 KB page cache; raises TLBException on miss/invalid/mod."""
        hit = self.tlb_cache.get(addr >> 12)
        if hit is not None:
            base, dirty = hit
            if write and not dirty:
                raise TLBException(1, addr, False)
            return base | (addr & 0xFFF)
        cpu = self.core.cpu
        asid = cpu.cp0[CP0_ENTRYHI] & 0xFF
        for e in cpu.tlb:
            mask = (e.mask >> 13) & 0xFFF               # PageMask bits 24..13
            if ((addr >> 13) & ~mask & 0x7FFFF) != (e.vpn2 & ~mask & 0x7FFFF):
                continue
            if not (e.g or e.asid == asid):
                continue
            page_bits = 12 + (mask.bit_length() if mask else 0)
            odd = (addr >> page_bits) & 1
            v, d, pfn = (e.v1, e.d1, e.pfn1) if odd else (e.v0, e.d0, e.pfn0)
            if not v:
                raise TLBException(3 if write else 2, addr, False)
            if write and not d:
                raise TLBException(1, addr, False)
            off_mask = (1 << page_bits) - 1
            phys = ((pfn << 12) & ~off_mask) | (addr & off_mask)
            self.tlb_cache[addr >> 12] = (phys & ~0xFFF, d)
            return phys
        raise TLBException(3 if write else 2, addr, True)

    def read_u8(self, addr):
        p = self.v_to_p(addr)
        if 0 <= p < RDRAM_SIZE: return self.core.rdram[p]
        if 0x04000000 <= p < 0x04002000:
            off = p - 0x04000000
            return (self.core.rsp_dmem if off < 0x1000 else self.core.rsp_imem)[off & 0xFFF]
        if 0x10000000 <= p < 0x10000000 + len(self.core.rom): return self.core.rom[p - 0x10000000]
        if 0x1FC007C0 <= p < 0x1FC007C0 + PIF_RAM_SIZE: return self.core.pif_ram[p - 0x1FC007C0]
        return 0

    def read_u16(self, addr):
        p = self.v_to_p(addr)
        rdram = self.core.rdram
        if 0 <= p < RDRAM_SIZE - 1: return (rdram[p] << 8) | rdram[p + 1]
        if 0x04000000 <= p < 0x04002000 - 1:
            off = p - 0x04000000
            buf = self.core.rsp_dmem if off < 0x1000 else self.core.rsp_imem
            return (buf[off & 0xFFF] << 8) | buf[(off & 0xFFF) + 1]
        return 0

    def read_u32(self, addr):
        # UltraHLE OS segment: thread RA lands on PATCH(osStopCurrentThread).
        if (addr & 0x1FFFFFFF) == (ULTRAHLE_OS_SEG & 0x1FFFFFFF):
            return make_ultrahle_patch(28)
        p = self.v_to_p(addr)
        rdram = self.core.rdram
        if p <= RDRAM_SIZE - 4:
            # Hot path: RDRAM fetch without bounds re-checks in the common case.
            return (rdram[p] << 24) | (rdram[p + 1] << 16) | (rdram[p + 2] << 8) | rdram[p + 3]
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            return (buf[off] << 24) | (buf[off + 1] << 16) | (buf[off + 2] << 8) | buf[off + 3]
        if 0x04040000 <= p <= 0x048FFFFF: return self._read_mmio(p)
        if 0x08000000 <= p < 0x10000000: return self.core.save_mgr.cart2_read32(p - 0x08000000)
        roff = p - 0x10000000
        rom = self.core.rom
        if 0 <= roff <= len(rom) - 4:
            return (rom[roff] << 24) | (rom[roff + 1] << 16) | (rom[roff + 2] << 8) | rom[roff + 3]
        return 0

    def read_u64(self, addr): return (self.read_u32(addr) << 32) | self.read_u32(addr + 4)

    def _read_mmio(self, p):
        al = p & ~3
        if al == SP_STATUS: return self.sp_status
        if al in (SP_DMA_FULL, SP_DMA_BUSY): return 0
        if al == SP_PC: return self.core.rsp_pc
        if al == DPC_STATUS: return self.dpc_status
        if al == MI_MODE: return self.mi_mode
        if al == MI_VERSION: return self.mi_version
        if al == MI_INTR: return self.hw_interrupts
        if al == MI_INTR_MASK: return self.mi_intr_mask
        if al == VI_V_CURRENT: return self.core.vi_current_line() if self.core.lle else self.half_line
        if VI_STATUS <= al <= VI_Y_SCALE: return self.regs.get(al, 0)
        if AI_DRAM_ADDR <= al <= AI_BITRATE: return self.regs.get(al, 0)
        if al == AI_STATUS: return self.core.ai_status() if self.core.lle else self.regs.get(al, 0)
        if al == AI_LEN and self.core.lle: return self.core.ai_len_remaining()
        if al == PI_STATUS and self.core.lle:
            return (0x3 if "PI" in self.core.events else 0) | (0x8 if self.hw_interrupts & MI_INTR_PI else 0)
        if PI_DRAM_ADDR <= al <= PI_DOM2_RLS: return self.regs.get(al, 0)
        if al == SI_STATUS:
            if not self.core.lle: return 0
            return (0x1 if "SI" in self.core.events else 0) | (SI_STATUS_INTERRUPT if self.hw_interrupts & MI_INTR_SI else 0)
        if SI_DRAM_ADDR <= al <= SI_PIF_ADDR_WR: return self.regs.get(al, 0)
        if RI_MODE <= al <= RI_WERROR: return self.regs.get(al, 0)
        if al in (DPC_START, DPC_END, DPC_CURRENT, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM): return self.regs.get(al, 0)
        if al in (DPS_TBIST, DPS_TEST_MODE, DPS_BUFTEST, DPS_DETAIL): return self.dps_regs.get(al, 0)
        return self.regs.get(al, 0)

    def write_u8(self, addr, val):
        p = self.v_to_p(addr, True)
        val &= MASK_8
        if 0 <= p < RDRAM_SIZE:
            self.core.rdram[p] = val
            if (p >> 12) in self.core.jit.page_blocks: self.core.jit.invalidate_page(p >> 12)
            return
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = val; return
        if 0x1FC007C0 <= p < 0x1FC007C0 + PIF_RAM_SIZE: self.core.pif_ram[p - 0x1FC007C0] = val

    def write_u16(self, addr, val):
        p = self.v_to_p(addr, True)
        if 0 <= p < RDRAM_SIZE - 1:
            rdram = self.core.rdram; val &= MASK_16
            rdram[p] = (val >> 8) & MASK_8; rdram[p + 1] = val & MASK_8
            if (p >> 12) in self.core.jit.page_blocks: self.core.jit.invalidate_page(p >> 12)
            return
        if 0x04000000 <= p < 0x04002000 - 1:
            off = p & 0xFFF; val &= MASK_16
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = (val >> 8) & MASK_8; buf[off + 1] = val & MASK_8

    def write_u32(self, addr, val):
        p = self.v_to_p(addr, True)
        rdram = self.core.rdram
        if p <= RDRAM_SIZE - 4 >= 0:
            val &= MASK_32
            rdram[p] = (val >> 24) & MASK_8; rdram[p + 1] = (val >> 16) & MASK_8
            rdram[p + 2] = (val >> 8) & MASK_8; rdram[p + 3] = val & MASK_8
            if (p >> 12) in self.core.jit.page_blocks: self.core.jit.invalidate_page(p >> 12)
            return
        if 0x04000000 <= p < 0x04002000:
            off = p & 0xFFF; val &= MASK_32
            buf = self.core.rsp_dmem if p < 0x04001000 else self.core.rsp_imem
            buf[off] = (val >> 24) & MASK_8; buf[off + 1] = (val >> 16) & MASK_8
            buf[off + 2] = (val >> 8) & MASK_8; buf[off + 3] = val & MASK_8; return
        if 0x04040000 <= p <= 0x048FFFFF: self._write_mmio(p, val)
        elif 0x08000000 <= p < 0x10000000: self.core.save_mgr.cart2_write32(p - 0x08000000, val & MASK_32)

    def write_u64(self, addr, val):
        val &= MASK_64; self.write_u32(addr, (val >> 32) & MASK_32); self.write_u32(addr + 4, val & MASK_32)

    def _change_sp_status(self, mv):
        if mv & SP_CLR_HALT: self.sp_status &= ~SP_STATUS_HALT
        if mv & SP_SET_HALT: self.sp_status |= SP_STATUS_HALT
        if mv & SP_CLR_BROKE: self.sp_status &= ~SP_STATUS_BROKE
        if mv & SP_CLR_INTR: self.hw_interrupts &= ~MI_INTR_SP
        if mv & SP_SET_INTR: self.hw_interrupts |= MI_INTR_SP
        if mv & SP_CLR_SSTEP: self.sp_status &= ~SP_STATUS_SSTEP
        if mv & SP_SET_SSTEP: self.sp_status |= SP_STATUS_SSTEP
        if mv & SP_CLR_INTR_BREAK: self.sp_status &= ~SP_STATUS_INTR_BREAK
        if mv & SP_SET_INTR_BREAK: self.sp_status |= SP_STATUS_INTR_BREAK
        for i in range(8):
            clr = [SP_CLR_SIG0,SP_CLR_SIG1,SP_CLR_SIG2,SP_CLR_SIG3,SP_CLR_SIG4,SP_CLR_SIG5,SP_CLR_SIG6,SP_CLR_SIG7][i]
            set_ = [SP_SET_SIG0,SP_SET_SIG1,SP_SET_SIG2,SP_SET_SIG3,SP_SET_SIG4,SP_SET_SIG5,SP_SET_SIG6,SP_SET_SIG7][i]
            if mv & clr: self.sp_status &= ~(0x80 << i)
            if mv & set_: self.sp_status |= (0x80 << i)
        if (mv & SP_SET_SIG0) and self.core.audio_signal and not self.core.lle: self.hw_interrupts |= MI_INTR_SP
        if not (self.sp_status & SP_STATUS_HALT) and not self.core.rsp_busy: self.core.process_rsp()

    def _change_dpc_status(self, mv):
        if mv & DPC_CLR_XBUS_DMEM_DMA: self.dpc_status &= ~DPC_STATUS_XBUS_DMEM_DMA
        if mv & DPC_SET_XBUS_DMEM_DMA: self.dpc_status |= DPC_STATUS_XBUS_DMEM_DMA
        if mv & DPC_CLR_FREEZE: self.dpc_status &= ~DPC_STATUS_FREEZE
        if mv & DPC_SET_FREEZE: self.dpc_status |= DPC_STATUS_FREEZE
        if mv & DPC_CLR_FLUSH: self.dpc_status &= ~DPC_STATUS_FLUSH
        if mv & DPC_SET_FLUSH: self.dpc_status |= DPC_STATUS_FLUSH
        if (mv & DPC_CLR_FREEZE) and not (self.sp_status & SP_STATUS_HALT) and not (self.sp_status & SP_STATUS_BROKE):
            self.core.process_rsp()

    def _change_mi_mode(self, mv):
        self.mi_mode = (self.mi_mode & ~0x7F) | (mv & 0x7F)
        if mv & MI_CLR_INIT: self.mi_mode &= ~MI_MODE_INIT
        if mv & MI_SET_INIT: self.mi_mode |= MI_MODE_INIT
        if mv & MI_CLR_EBUS: self.mi_mode &= ~MI_MODE_EBUS
        if mv & MI_SET_EBUS: self.mi_mode |= MI_MODE_EBUS
        if mv & MI_CLR_DP_INTR: self.hw_interrupts &= ~MI_INTR_DP
        if mv & MI_CLR_RDRAM: self.mi_mode &= ~MI_MODE_RDRAM
        if mv & MI_SET_RDRAM: self.mi_mode |= MI_MODE_RDRAM

    def _change_mi_intr_mask(self, mv):
        if mv & MI_INTR_MASK_CLR_SP: self.mi_intr_mask &= ~MI_INTR_SP
        if mv & MI_INTR_MASK_SET_SP: self.mi_intr_mask |= MI_INTR_SP
        if mv & MI_INTR_MASK_CLR_SI: self.mi_intr_mask &= ~MI_INTR_SI
        if mv & MI_INTR_MASK_SET_SI: self.mi_intr_mask |= MI_INTR_SI
        if mv & MI_INTR_MASK_CLR_AI: self.mi_intr_mask &= ~MI_INTR_AI
        if mv & MI_INTR_MASK_SET_AI: self.mi_intr_mask |= MI_INTR_AI
        if mv & MI_INTR_MASK_CLR_VI: self.mi_intr_mask &= ~MI_INTR_VI
        if mv & MI_INTR_MASK_SET_VI: self.mi_intr_mask |= MI_INTR_VI
        if mv & MI_INTR_MASK_CLR_PI: self.mi_intr_mask &= ~MI_INTR_PI
        if mv & MI_INTR_MASK_SET_PI: self.mi_intr_mask |= MI_INTR_PI
        if mv & MI_INTR_MASK_CLR_DP: self.mi_intr_mask &= ~MI_INTR_DP
        if mv & MI_INTR_MASK_SET_DP: self.mi_intr_mask |= MI_INTR_DP

    def _write_mmio(self, p, val):
        al = p & ~3
        if al in (SP_MEM_ADDR, SP_DRAM_ADDR, SP_RD_LEN, SP_WR_LEN, SP_SEMAPHORE, SP_PC, SP_IBIST):
            self.regs[al] = val
            if al == SP_RD_LEN: self.core.trigger_sp_dma(to_rsp=True)
            elif al == SP_WR_LEN: self.core.trigger_sp_dma(to_rsp=False)
            elif al == SP_PC: self.core.rsp_pc = val
        elif al == SP_STATUS: self._change_sp_status(val)
        elif al == DPC_STATUS: self._change_dpc_status(val)
        elif al in (DPC_START, DPC_END, DPC_CURRENT, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM):
            if al == DPC_START:
                self.regs[DPC_CURRENT] = val & 0xFFFFF8
            if al == DPC_END:
                if self.core.lle:
                    self.regs[DPC_CURRENT] = self.core.process_rdp_commands(
                        self.regs.get(DPC_CURRENT, self.regs.get(DPC_START, 0)), val,
                        xbus=bool(self.dpc_status & DPC_STATUS_XBUS_DMEM_DMA))
                    self.regs[DPC_END] = val & 0xFFFFF8
                    return
                self.core.process_rdp()
                self.regs[DPC_CURRENT] = val
            self.regs[al] = val
        elif al in (DPS_TBIST, DPS_TEST_MODE, DPS_BUFTEST, DPS_DETAIL): self.dps_regs[al] = val
        elif al == MI_MODE: self._change_mi_mode(val)
        elif al == MI_INTR: self.hw_interrupts &= ~val
        elif al == MI_INTR_MASK: self._change_mi_intr_mask(val)
        elif al == VI_ORIGIN:
            self.regs[VI_ORIGIN] = val
            if (val & 0xFFFFFF) != 0:
                self.core._vi_origin_set = True
                # Present as soon as the game programs a framebuffer — don't wait
                # for the next VI retrace or the UI stays on the Booting prompt.
                self.core.render_vi()
        elif al in (VI_STATUS, VI_WIDTH, VI_BURST, VI_V_SYNC, VI_H_SYNC, VI_LEAP, VI_H_START, VI_V_START, VI_V_BURST, VI_X_SCALE, VI_Y_SCALE):
            self.regs[al] = val
            if al == VI_WIDTH and (self.regs.get(VI_ORIGIN, 0) & 0xFFFFFF):
                self.core.render_vi()
        elif al == VI_INTR: self.regs[VI_INTR] = val & 0x3FF; self.half_line = 0
        elif al == VI_V_CURRENT: self.hw_interrupts &= ~MI_INTR_VI  # any write acks VI
        elif al == AI_DRAM_ADDR: self.regs[AI_DRAM_ADDR] = val & 0x00FFFFFF
        elif al == AI_LEN:
            self.regs[AI_LEN] = val
            if self.core.lle: self.core.ai_push(self.regs.get(AI_DRAM_ADDR, 0), val & 0x3FFF8)
            else: self.core.process_audio()
        elif al == AI_STATUS: self.hw_interrupts &= ~MI_INTR_AI  # any write acks AI
        elif al == AI_CONTROL: self.regs[AI_CONTROL] = val; self.regs[AI_STATUS] = self.regs.get(AI_STATUS,0) & ~AI_STATUS_DMA_BUSY
        elif al in (AI_DACRATE, AI_BITRATE): self.regs[al] = val
        elif al == PI_DRAM_ADDR: self.regs[PI_DRAM_ADDR] = val & 0x00FFFFFF
        elif al == PI_CART_ADDR: self.regs[PI_CART_ADDR] = val
        elif al == PI_RD_LEN: self.regs[PI_RD_LEN] = val; self.core.trigger_pi_dma()
        elif al == PI_WR_LEN: self.regs[PI_WR_LEN] = val; self.core.trigger_pi_dma()
        elif al == PI_STATUS:
            if val & 1: self.regs[PI_STATUS] = 0  # reset controller
            if val & 2: self.hw_interrupts &= ~MI_INTR_PI
        elif PI_DOM1_LAT <= al <= PI_DOM2_RLS: self.regs[al] = val
        elif al == SI_DRAM_ADDR: self.regs[SI_DRAM_ADDR] = val
        elif al == SI_STATUS: self.hw_interrupts &= ~MI_INTR_SI  # any write acks SI
        elif al == SI_PIF_ADDR_RD: self.core.trigger_si_dma(read_pif=True)
        elif al == SI_PIF_ADDR_WR: self.core.trigger_si_dma(read_pif=False)
        elif RI_MODE <= al <= RI_WERROR: self.regs[al] = val
        else: self.regs[al] = val

# ── CPUCore (R4300i interpreter) ──
class CPUCore:
    def __init__(self, core):
        self.core = core
        self.gpr = [0] * 32
        self.fpr = [0] * 32
        self.cp0 = [0] * 32
        self.fcr0 = 0x00000511
        self.fcr31 = 0
        self.hi = 0
        self.lo = 0
        self.pc = 0
        self.next_pc = 4
        self.llbit = False
        self.lladdr = 0
        self.tlb = [TLBEntry() for _ in range(32)]
        self.in_delay = False       # instruction being executed sits in a branch delay slot
        self.count_per_op = 1       # COUNT ticks per instruction (accurate mode uses 2)
        self.idle = False           # set by a branch-to-self (idle loop) for fast-forward
        self.reset()

    def reset(self):
        self.gpr = [0] * 32; self.fpr = [0] * 32; self.cp0 = [0] * 32
        self.fcr0 = 0x00000511; self.fcr31 = 0; self.hi = 0; self.lo = 0; self.pc = 0; self.next_pc = 4
        self.cp0[CP0_PRID] = 0x00000B00; self.cp0[CP0_STATUS] = 0x34000000; self.cp0[CP0_CONFIG] = 0x7006E463
        self.cp0[CP0_WIRED] = 0; self.cp0[CP0_CONTEXT] = 0x007FFFF0; self.cp0[CP0_EPC] = 0xFFFFFFFF
        self.cp0[CP0_BADVADDR] = 0xFFFFFFFF; self.cp0[CP0_ERROREPC] = 0xFFFFFFFF; self.cp0[CP0_CAUSE] = 0xB000005C
        self.llbit = False; self.lladdr = 0; self.tlb = [TLBEntry() for _ in range(32)]

    def step(self):
        bus = self.core.bus
        cp0 = self.cp0
        status = cp0[CP0_STATUS]
        # RCP (MI) interrupts all share CPU IP2. Timer uses IP7 via COMPARE.
        pending_rcp = bus.hw_interrupts & bus.mi_intr_mask & 0x3F
        if pending_rcp:
            cp0[CP0_CAUSE] = (cp0[CP0_CAUSE] & ~CAUSE_IP2) | CAUSE_IP2
        else:
            cp0[CP0_CAUSE] &= ~CAUSE_IP2
        if (status & STATUS_IE) and not (status & (STATUS_EXL | STATUS_ERL)):
            cause = cp0[CP0_CAUSE]
            # Fire if any Cause IP bit is enabled in Status IM (bits 8..15).
            if (cause & status & 0xFF00) != 0:
                self.in_delay = self.next_pc != ((self.pc + 4) & MASK_32)
                self._raise_exception(0, self.pc)
        try:
            word = bus.read_u32(self.pc)
        except TLBException as e:
            self.in_delay = self.next_pc != ((self.pc + 4) & MASK_32)
            self._tlb_exception(e, self.pc)
            word = bus.read_u32(self.pc)
        self.execute(get_opcode(word))
        self.gpr[0] = 0
        # COUNT runs at half the CPU clock; count_per_op models average CPI.
        old = cp0[CP0_COUNT]
        cpo = self.count_per_op
        cp0[CP0_COUNT] = (old + cpo) & MASK_32
        if ((cp0[CP0_COMPARE] - old - 1) & MASK_32) < cpo:
            cp0[CP0_CAUSE] |= CAUSE_IP7  # timer interrupt only — never fake SP

    def step_block(self, n: int) -> int:
        """Run up to n instructions; return how many actually executed."""
        ran = 0
        g0 = self.gpr
        while ran < n:
            self.step()
            g0[0] = 0
            ran += 1
            if not self.core.running:
                break
        return ran

    def _branch(self, target): self.next_pc = u32(target)
    def _skip_likely(self): self.pc = u32(self.pc + 4); self.next_pc = u32(self.pc + 4)

    def _write_tlb_entry(self, index):
        self.core.bus.tlb_cache.clear()
        self.core.jit.invalidate_mapped()
        idx = index % 32; hi = self.cp0[CP0_ENTRYHI]; lo0 = self.cp0[CP0_ENTRYLO0]; lo1 = self.cp0[CP0_ENTRYLO1]
        pm = self.cp0[CP0_PAGEMASK]
        self.tlb[idx].mask = pm; self.tlb[idx].vpn2 = (hi >> 13) & 0x7FFFF; self.tlb[idx].asid = hi & 0xFF
        self.tlb[idx].g = bool((lo0 & 1) and (lo1 & 1))
        self.tlb[idx].pfn0 = (lo0 >> 6) & 0xFFFFF; self.tlb[idx].c0 = (lo0 >> 3) & 7
        self.tlb[idx].d0 = bool((lo0 >> 2) & 1); self.tlb[idx].v0 = bool((lo0 >> 1) & 1)
        self.tlb[idx].pfn1 = (lo1 >> 6) & 0xFFFFF; self.tlb[idx].c1 = (lo1 >> 3) & 7
        self.tlb[idx].d1 = bool((lo1 >> 2) & 1); self.tlb[idx].v1 = bool((lo1 >> 1) & 1)

    def _raise_exception(self, exc_code, old_pc, refill=False, ce=0):
        """VR4300 exception entry: ExcCode, BD/EPC (delay slot), EXL, vector."""
        cp0 = self.cp0
        cause = (cp0[CP0_CAUSE] & ~(0x7C | 0x30000000)) | ((exc_code & 0x1F) << 2) | ((ce & 3) << 28)
        status = cp0[CP0_STATUS]
        if not (status & STATUS_EXL):
            if self.in_delay:
                cp0[CP0_EPC] = u32(old_pc - 4); cause |= CAUSE_BD
            else:
                cp0[CP0_EPC] = u32(old_pc); cause &= ~CAUSE_BD
            off = 0x000 if refill else 0x180
        else:
            off = 0x180
        cp0[CP0_CAUSE] = cause & MASK_32
        cp0[CP0_STATUS] = status | STATUS_EXL
        base = 0xBFC00200 if status & STATUS_BEV else 0x80000000
        self.pc = base + off; self.next_pc = self.pc + 4
        self.in_delay = False

    def _tlb_exception(self, e, old_pc):
        cp0 = self.cp0
        va = e.vaddr & MASK_32
        cp0[CP0_BADVADDR] = va
        cp0[CP0_CONTEXT] = (cp0[CP0_CONTEXT] & 0xFF800000) | ((va >> 9) & 0x007FFFF0)
        cp0[CP0_ENTRYHI] = (va & 0xFFFFE000) | (cp0[CP0_ENTRYHI] & 0xFF)
        self._raise_exception(e.code, old_pc, refill=e.refill)

    def _test_cop1_usable(self): return bool(self.cp0[CP0_STATUS] & STATUS_CU1)

    # FPU register file. Status.FR=0 (o32 games): 16 64-bit regs; odd fN is the high half of f(N-1).
    def fget32(self, i):
        if self.cp0[CP0_STATUS] & STATUS_FR or not (i & 1): return self.fpr[i] & MASK_32
        return self.fpr[i - 1] >> 32
    def fset32(self, i, v):
        v &= MASK_32
        if self.cp0[CP0_STATUS] & STATUS_FR or not (i & 1):
            self.fpr[i] = (self.fpr[i] & 0xFFFFFFFF00000000) | v
        else:
            self.fpr[i - 1] = (self.fpr[i - 1] & MASK_32) | (v << 32)
    def fget64(self, i):
        return self.fpr[i if self.cp0[CP0_STATUS] & STATUS_FR else i & ~1]
    def fset64(self, i, v):
        self.fpr[i if self.cp0[CP0_STATUS] & STATUS_FR else i & ~1] = v & MASK_64
    def _clear_fp_cause(self): self.fcr31 &= ~0x3F000
    def _set_fp_cause(self, cause): self.fcr31 &= ~0x3F000; self.fcr31 |= (cause & 0x3F) << 12
    def _set_fp_flags(self, cause): self.fcr31 |= (cause & 0x3F) << 2

    def execute(self, o):
        old_pc = self.pc
        npc = self.next_pc
        self.in_delay = npc != ((old_pc + 4) & MASK_32)
        self.pc = npc
        self.next_pc = (npc + 4) & MASK_32
        h = _DISPATCH[o.instr_id]
        if h is not None:
            try:
                h(self, o, old_pc, self.gpr)
            except TLBException as e:
                self._tlb_exception(e, old_pc)
        elif o.op in (0x10, 0x11, 0x12, 0x13):
            self.core.note_unimpl(f"cpu:CpU:{o.word:08X}")
            self._raise_exception(11, old_pc, ce=o.op & 3)
        else:
            self.core.note_unimpl(f"cpu:RI:{o.word:08X}")
            self._raise_exception(10, old_pc)

# ── Instruction handlers ──
def _h_NOP(cpu, o, old_pc, g): pass
def _h_LUI(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(o.imm << 16)
def _h_ORI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] | o.imm)
def _h_ANDI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] & o.imm)
def _h_XORI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] ^ o.imm)
def _h_ADDI(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(u32(g[o.rs] + o.simm))
def _h_ADDIU(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(u32(g[o.rs] + o.simm))
def _h_DADDI(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] + o.simm)
def _h_DADDIU(cpu, o, old_pc, g): g[o.rt] = u64(g[o.rs] + o.simm)
def _h_SLTI(cpu, o, old_pc, g): g[o.rt] = 1 if sign64(g[o.rs]) < o.simm else 0
def _h_SLTIU(cpu, o, old_pc, g): g[o.rt] = 1 if g[o.rs] < u64(o.simm) else 0
def _h_LB(cpu, o, old_pc, g): g[o.rt] = sx8_to_64(cpu.core.bus.read_u8(g[o.rs] + o.simm))
def _h_LBU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u8(g[o.rs] + o.simm)
def _h_LH(cpu, o, old_pc, g): g[o.rt] = sx16_to_64(cpu.core.bus.read_u16(g[o.rs] + o.simm))
def _h_LHU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u16(g[o.rs] + o.simm)
def _h_LW(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.core.bus.read_u32(g[o.rs] + o.simm))
def _h_LWU(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u32(g[o.rs] + o.simm)
def _h_LD(cpu, o, old_pc, g): g[o.rt] = cpu.core.bus.read_u64(g[o.rs] + o.simm)
def _h_LWL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    g[o.rt] = sx32_to_64((u32(g[o.rt]) & _lwl_mask[off]) | (val << _lwl_shift[off]))
def _h_LWR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    g[o.rt] = sx32_to_64((u32(g[o.rt]) & _lwr_mask[off]) | (val >> _lwr_shift[off]))
def _h_LDL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    g[o.rt] = (g[o.rt] & _ldl_mask[off]) | (val << _ldl_shift[off])
def _h_LDR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    g[o.rt] = (g[o.rt] & _ldr_mask[off]) | (val >> _ldr_shift[off])
def _h_LL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); g[o.rt] = sx32_to_64(cpu.core.bus.read_u32(addr))
    cpu.llbit = True; cpu.lladdr = addr & ~3
def _h_LLD(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); g[o.rt] = cpu.core.bus.read_u64(addr)
    cpu.llbit = True; cpu.lladdr = addr & ~7
def _h_LWC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    addr = u32(g[o.rs] + o.simm)
    cpu.fset32(o.rt, cpu.core.bus.read_u32(addr))
def _h_LDC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu.fset64(o.rt, cpu.core.bus.read_u64(u32(g[o.rs] + o.simm)))
def _h_SB(cpu, o, old_pc, g): cpu.core.bus.write_u8(u32(g[o.rs] + o.simm), u8(g[o.rt]))
def _h_SH(cpu, o, old_pc, g): cpu.core.bus.write_u16(u32(g[o.rs] + o.simm), u16(g[o.rt]))
def _h_SW(cpu, o, old_pc, g): cpu.core.bus.write_u32(u32(g[o.rs] + o.simm), u32(g[o.rt]))
def _h_SD(cpu, o, old_pc, g): cpu.core.bus.write_u64(u32(g[o.rs] + o.simm), g[o.rt])
def _h_SWL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    val = (val & _swl_mask[off]) | (u32(g[o.rt]) >> _swl_shift[off])
    cpu.core.bus.write_u32(al, val)
def _h_SWR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 3; al = addr & ~3
    val = cpu.core.bus.read_u32(al)
    val = (val & _swr_mask[off]) | (u32(g[o.rt]) << _swr_shift[off])
    cpu.core.bus.write_u32(al, val)
def _h_SDL(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    val = (val & _sdl_mask[off]) | (g[o.rt] >> _sdl_shift[off])
    cpu.core.bus.write_u64(al, val)
def _h_SDR(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm); off = addr & 7; al = addr & ~7
    val = cpu.core.bus.read_u64(al)
    val = (val & _sdr_mask[off]) | (g[o.rt] << _sdr_shift[off])
    cpu.core.bus.write_u64(al, val)
def _h_SC(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm)
    if cpu.llbit and (addr & ~3) == cpu.lladdr:
        cpu.core.bus.write_u32(addr, u32(g[o.rt])); g[o.rt] = 1
    else: g[o.rt] = 0
    cpu.llbit = False
def _h_SCD(cpu, o, old_pc, g):
    addr = u32(g[o.rs] + o.simm)
    if cpu.llbit and (addr & ~7) == cpu.lladdr:
        cpu.core.bus.write_u64(addr, g[o.rt]); g[o.rt] = 1
    else: g[o.rt] = 0
    cpu.llbit = False
def _h_SWC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu.core.bus.write_u32(u32(g[o.rs] + o.simm), cpu.fget32(o.rt))
def _h_SDC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu.core.bus.write_u64(u32(g[o.rs] + o.simm), cpu.fget64(o.rt))

# SPECIAL opcodes
def _h_SLL(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) << o.sa)
def _h_SRL(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) >> o.sa)
def _h_SRA(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(sign32(g[o.rt]) >> o.sa)
def _h_SLLV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) << (g[o.rs] & 0x1F))
def _h_SRLV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rt]) >> (g[o.rs] & 0x1F))
def _h_SRAV(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(sign32(g[o.rt]) >> (g[o.rs] & 0x1F))
def _h_DSLLV(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << (g[o.rs] & 0x3F))
def _h_DSRLV(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> (g[o.rs] & 0x3F))
def _h_DSRAV(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> (g[o.rs] & 0x3F))
def _h_DSLL(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << o.sa)
def _h_DSRL(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> o.sa)
def _h_DSRA(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> o.sa)
def _h_DSLL32(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] << (o.sa + 32))
def _h_DSRL32(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rt] >> (o.sa + 32))
def _h_DSRA32(cpu, o, old_pc, g): g[o.rd] = u64(sign64(g[o.rt]) >> (o.sa + 32))
def _h_ADD(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] + g[o.rt]))
def _h_ADDU(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] + g[o.rt]))
def _h_SUB(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] - g[o.rt]))
def _h_SUBU(cpu, o, old_pc, g): g[o.rd] = sx32_to_64(u32(g[o.rs] - g[o.rt]))
def _h_DADD(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] + g[o.rt])
def _h_DADDU(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] + g[o.rt])
def _h_DSUB(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] - g[o.rt])
def _h_DSUBU(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] - g[o.rt])
def _h_AND(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] & g[o.rt])
def _h_OR(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] | g[o.rt])
def _h_XOR(cpu, o, old_pc, g): g[o.rd] = u64(g[o.rs] ^ g[o.rt])
def _h_NOR(cpu, o, old_pc, g): g[o.rd] = u64(~(g[o.rs] | g[o.rt]))
def _h_MOVZ(cpu, o, old_pc, g):
    if g[o.rt] == 0: g[o.rd] = g[o.rs]
def _h_MOVN(cpu, o, old_pc, g):
    if g[o.rt] != 0: g[o.rd] = g[o.rs]
def _h_SLT(cpu, o, old_pc, g): g[o.rd] = 1 if sign64(g[o.rs]) < sign64(g[o.rt]) else 0
def _h_SLTU(cpu, o, old_pc, g): g[o.rd] = 1 if g[o.rs] < g[o.rt] else 0
def _h_MFHI(cpu, o, old_pc, g): g[o.rd] = cpu.hi
def _h_MTHI(cpu, o, old_pc, g): cpu.hi = u64(g[o.rs])
def _h_MFLO(cpu, o, old_pc, g): g[o.rd] = cpu.lo
def _h_MTLO(cpu, o, old_pc, g): cpu.lo = u64(g[o.rs])
def _h_MULT(cpu, o, old_pc, g):
    prod = sign32(g[o.rs]) * sign32(g[o.rt])
    cpu.lo = sx32_to_64(prod & MASK_32); cpu.hi = sx32_to_64((prod >> 32) & MASK_32)
def _h_MULTU(cpu, o, old_pc, g):
    prod = u32(g[o.rs]) * u32(g[o.rt])
    cpu.lo = sx32_to_64(prod & MASK_32); cpu.hi = sx32_to_64((prod >> 32) & MASK_32)
def _h_DMULT(cpu, o, old_pc, g):
    prod = sign64(g[o.rs]) * sign64(g[o.rt]); cpu.lo = u64(prod); cpu.hi = u64(prod >> 64)
def _h_DMULTU(cpu, o, old_pc, g):
    prod = g[o.rs] * g[o.rt]; cpu.lo = u64(prod); cpu.hi = u64(prod >> 64)
def _tdiv(a, b):
    """MIPS signed division: quotient truncates toward zero, remainder takes the dividend's sign."""
    q = abs(a) // abs(b)
    if (a < 0) != (b < 0): q = -q
    return q, a - q * b
def _h_DIV(cpu, o, old_pc, g):
    a_s = sign32(g[o.rs]); b_s = sign32(g[o.rt])
    if b_s != 0:
        q, r = _tdiv(a_s, b_s)
        cpu.lo = sx32_to_64(q & MASK_32); cpu.hi = sx32_to_64(r & MASK_32)
    else:
        cpu.lo = 1 if a_s < 0 else MASK_64; cpu.hi = sx32_to_64(a_s & MASK_32)
def _h_DIVU(cpu, o, old_pc, g):
    a = u32(g[o.rs]); b = u32(g[o.rt])
    if b != 0: cpu.lo = sx32_to_64(a // b); cpu.hi = sx32_to_64(a % b)
    else: cpu.lo = MASK_64; cpu.hi = sx32_to_64(a)
def _h_DDIV(cpu, o, old_pc, g):
    a = sign64(g[o.rs]); b = sign64(g[o.rt])
    if b != 0:
        q, r = _tdiv(a, b)
        cpu.lo = u64(q); cpu.hi = u64(r)
    else: cpu.lo = 1 if a < 0 else MASK_64; cpu.hi = u64(a)
def _h_DDIVU(cpu, o, old_pc, g):
    a = g[o.rs]; b = g[o.rt]
    if b != 0: cpu.lo = u64(a // b); cpu.hi = u64(a % b)
    else: cpu.lo = MASK_64; cpu.hi = u64(a)

# REGIMM
def _h_BLTZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGEZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BLTZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGEZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BLTZAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGEZAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BLTZALL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) < 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGEZALL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8)
    if sign64(g[o.rs]) >= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_J(cpu, o, old_pc, g):
    t = o.target_addr(old_pc)
    if t == old_pc: cpu.idle = True
    cpu._branch(t)
def _h_JAL(cpu, o, old_pc, g):
    g[31] = u64(old_pc + 8); cpu._branch(o.target_addr(old_pc))
def _h_JR(cpu, o, old_pc, g): cpu._branch(g[o.rs])
def _h_JALR(cpu, o, old_pc, g):
    g[o.rd] = u64(old_pc + 8); cpu._branch(g[o.rs])
def _h_BEQ(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]:
        if o.simm == -1: cpu.idle = True
        cpu._branch(o.branch_addr(old_pc))
def _h_BNE(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._branch(o.branch_addr(old_pc))
def _h_BLEZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) <= 0: cpu._branch(o.branch_addr(old_pc))
def _h_BGTZ(cpu, o, old_pc, g):
    if sign64(g[o.rs]) > 0: cpu._branch(o.branch_addr(old_pc))
def _h_BEQL(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BNEL(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BLEZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) <= 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()
def _h_BGTZL(cpu, o, old_pc, g):
    if sign64(g[o.rs]) > 0: cpu._branch(o.branch_addr(old_pc))
    else: cpu._skip_likely()

# COP0
def _h_MFC0(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.cp0[o.rd])
def _h_DMFC0(cpu, o, old_pc, g): g[o.rt] = u64(cpu.cp0[o.rd])
def _h_CFC0(cpu, o, old_pc, g): g[o.rt] = sx32_to_64(cpu.cp0[o.rd])
def _h_MTC0(cpu, o, old_pc, g):
    val = u32(g[o.rt]); rd = o.rd
    if rd == CP0_INDEX: cpu.cp0[rd] = val & 0x8000003F
    elif rd in (CP0_ENTRYLO0, CP0_ENTRYLO1): cpu.cp0[rd] = val & 0x3FFFFFFF
    elif rd == CP0_PAGEMASK: cpu.cp0[rd] = val & 0x01FFE000
    elif rd == CP0_WIRED: cpu.cp0[rd] = val & 0x3F; cpu.cp0[CP0_RANDOM] = 31
    elif rd == CP0_CONTEXT: cpu.cp0[rd] = (cpu.cp0[rd] & 0x7FFFFF) | (val & 0xFF800000)
    elif rd == CP0_COUNT:
        core = cpu.core
        if core.lle: core.sync_time(); core._count_at_now = val
        cpu.cp0[rd] = val
    elif rd == CP0_COMPARE: cpu.cp0[rd] = val; cpu.cp0[CP0_CAUSE] &= ~CAUSE_IP7
    elif rd == CP0_CAUSE: cpu.cp0[rd] = (cpu.cp0[rd] & ~0x300) | (val & 0x300)
    elif rd == CP0_ENTRYHI:
        if (cpu.cp0[rd] ^ val) & 0xFF:
            cpu.core.bus.tlb_cache.clear(); cpu.core.jit.invalidate_mapped()
        cpu.cp0[rd] = val & 0xFFFFE0FF
    elif rd in (CP0_STATUS, CP0_EPC, CP0_ERROREPC, CP0_LLADDR, CP0_CONFIG): cpu.cp0[rd] = val
    elif rd in (28, 29): cpu.cp0[rd] = val
def _h_DMTC0(cpu, o, old_pc, g):
    val = u64(g[o.rt]); rd = o.rd
    if rd == CP0_ENTRYHI: cpu.cp0[rd] = val & 0xFFFFFFFF
    elif rd == CP0_CONTEXT: cpu.cp0[rd] = (cpu.cp0[rd] & 0x7FFFFF) | (val & 0xFFFFFFFFFF800000)
    else: cpu.cp0[rd] = val
def _h_CTC0(cpu, o, old_pc, g): cpu.cp0[o.rd] = u32(g[o.rt])
def _h_BC0(cpu, o, old_pc, g):
    # VR4300 COP0 has no useful condition bit; treat condition as false.
    tf = o.rt & 1; likely = bool(o.rt & 2); cond = False
    if cond == bool(tf): cpu._branch(o.branch_addr(old_pc))
    elif likely: cpu._skip_likely()
def _h_ERET(cpu, o, old_pc, g):
    if cpu.cp0[CP0_STATUS] & STATUS_ERL:
        target = cpu.cp0[CP0_ERROREPC]
        cpu.cp0[CP0_STATUS] &= ~STATUS_ERL
    else:
        target = cpu.cp0[CP0_EPC]
        cpu.cp0[CP0_STATUS] &= ~STATUS_EXL
    cpu.pc = u32(target); cpu.next_pc = u32(cpu.pc + 4)
def _h_TLBWI(cpu, o, old_pc, g): cpu._write_tlb_entry(cpu.cp0[CP0_INDEX] & 0x1F)
def _h_TLBWR(cpu, o, old_pc, g):
    w = cpu.cp0[CP0_WIRED] & 0x1F; cpu._write_tlb_entry(random.randint(w, 31))
def _h_TLBP(cpu, o, old_pc, g):
    hi = cpu.cp0[CP0_ENTRYHI]; vpn2 = (hi >> 13) & 0x7FFFF; asid = hi & 0xFF
    match_i = -1
    for i, entry in enumerate(cpu.tlb):
        mask = (entry.mask >> 13) & 0xFFF
        if (entry.vpn2 & ~mask) == (vpn2 & ~mask) and (entry.g or entry.asid == asid): match_i = i; break
    cpu.cp0[CP0_INDEX] = match_i if match_i >= 0 else 0x80000000
def _h_TLBR(cpu, o, old_pc, g):
    idx = cpu.cp0[CP0_INDEX] & 0x1F; entry = cpu.tlb[idx]
    cpu.cp0[CP0_PAGEMASK] = entry.mask; cpu.cp0[CP0_ENTRYHI] = (entry.vpn2 << 13) | entry.asid
    cpu.cp0[CP0_ENTRYLO0] = (entry.pfn0 << 6) | (entry.c0 << 3) | (entry.d0 << 2) | (entry.v0 << 1) | entry.g
    cpu.cp0[CP0_ENTRYLO1] = (entry.pfn1 << 6) | (entry.c1 << 3) | (entry.d1 << 2) | (entry.v1 << 1) | entry.g

# COP1
def _h_MFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    g[o.rt] = sx32_to_64(cpu.fget32(o.rd))
def _h_DMFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    g[o.rt] = cpu.fget64(o.rd)
def _h_CFC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    g[o.rt] = sx32_to_64(cpu.fcr31 if o.rd == 31 else cpu.fcr0)
def _h_MTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu.fset32(o.rd, g[o.rt])
def _h_DMTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu.fset64(o.rd, g[o.rt])
def _h_CTC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    if o.rd == 31: cpu.fcr31 = u32(g[o.rt])
    elif o.rd == 0: cpu.fcr0 = u32(g[o.rt])
def _h_BC1(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    tf = o.rt & 1; likely = bool(o.rt & 2)
    cond = bool((cpu.fcr31 >> FCR31_COND_BIT) & 1)
    if cond == bool(tf): cpu._branch(o.branch_addr(old_pc))
    elif likely: cpu._skip_likely()

# Traps
def _h_SYSCALL(cpu, o, old_pc, g): cpu._raise_exception(8, old_pc)
def _h_BREAK(cpu, o, old_pc, g): cpu._raise_exception(9, old_pc)
def _h_TGE(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= sign64(g[o.rt]): cpu._raise_exception(13, old_pc)
def _h_TGEU(cpu, o, old_pc, g):
    if g[o.rs] >= g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TLT(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < sign64(g[o.rt]): cpu._raise_exception(13, old_pc)
def _h_TLTU(cpu, o, old_pc, g):
    if g[o.rs] < g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TEQ(cpu, o, old_pc, g):
    if g[o.rs] == g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TNE(cpu, o, old_pc, g):
    if g[o.rs] != g[o.rt]: cpu._raise_exception(13, old_pc)
def _h_TGEI(cpu, o, old_pc, g):
    if sign64(g[o.rs]) >= o.simm: cpu._raise_exception(13, old_pc)
def _h_TGEIU(cpu, o, old_pc, g):
    if g[o.rs] >= u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TLTI(cpu, o, old_pc, g):
    if sign64(g[o.rs]) < o.simm: cpu._raise_exception(13, old_pc)
def _h_TLTIU(cpu, o, old_pc, g):
    if g[o.rs] < u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TEQI(cpu, o, old_pc, g):
    if g[o.rs] == u64(o.simm): cpu._raise_exception(13, old_pc)
def _h_TNEI(cpu, o, old_pc, g):
    if g[o.rs] != u64(o.simm): cpu._raise_exception(13, old_pc)

# FPU format ops — full VR4300 COP1 S/D/W/L surface
def _fp_cmp(a, b, funct):
    nan = a != a or b != b
    f = funct & 7
    if f == 0: return False                      # C.F / C.SF
    if f == 1: return nan                        # C.UN / C.NGLE
    if f == 2: return (not nan) and a == b       # C.EQ / C.SEQ
    if f == 3: return nan or a == b              # C.UEQ / C.NGL
    if f == 4: return (not nan) and a < b        # C.OLT / C.LT
    if f == 5: return nan or a < b               # C.ULT / C.NGE
    if f == 6: return (not nan) and a <= b       # C.OLE / C.LE
    return nan or a <= b                         # C.ULE / C.NGT

def _fp_to_int(f, mode, bits):
    """Float → integer for ROUND/TRUNC/CEIL/FLOOR (mode 0..3) or CVT (mode -1 = FCR31.RM)."""
    if f != f or f in (float("inf"), float("-inf")):
        return (1 << (bits - 1)) - 1
    if mode == 0: v = round(f)                  # nearest, ties to even
    elif mode == 1: v = int(f)                  # toward zero
    elif mode == 2: v = math.ceil(f)
    else: v = math.floor(f)
    lim = 1 << (bits - 1)
    if v >= lim or v < -lim:
        return lim - 1  # invalid operation: VR4300 returns max positive
    return v & ((1 << bits) - 1)

def _h_FPU(cpu, o, old_pc, g):
    if not cpu._test_cop1_usable(): cpu._raise_exception(11, old_pc, ce=1); return
    cpu._clear_fp_cause()
    fmt_id = (o.instr_id >> 6) & 3; funct = o.instr_id & 0x3F
    fs, fd, ft = o.rd, o.sa, o.rt
    rm = cpu.fcr31 & 3
    if fmt_id == _ID_FPU_S or fmt_id == _ID_FPU_D:
        dbl = fmt_id == _ID_FPU_D
        if dbl:
            a = bits_to_f64(cpu.fget64(fs)); b = bits_to_f64(cpu.fget64(ft))
            put = lambda v: cpu.fset64(fd, f64_to_bits(v))
        else:
            a = bits_to_f32(cpu.fget32(fs)); b = bits_to_f32(cpu.fget32(ft))
            put = lambda v: cpu.fset32(fd, f32_to_bits(v))
        if funct == 0x00: put(a + b)
        elif funct == 0x01: put(a - b)
        elif funct == 0x02: put(a * b)
        elif funct == 0x03:
            if b == 0.0:
                cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
                put(float("nan") if a == 0.0 or a != a else math.copysign(float("inf"), a) * math.copysign(1.0, b))
            else:
                put(a / b)
        elif funct == 0x04: put(math.sqrt(a) if a >= 0 else float("nan"))
        elif funct == 0x05: put(abs(a))
        elif funct == 0x06:  # MOV
            if dbl: cpu.fset64(fd, cpu.fget64(fs))
            else: cpu.fset32(fd, cpu.fget32(fs))
        elif funct == 0x07: put(-a)
        elif funct == 0x15:  # RECIP
            if a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); cpu._set_fp_flags(FCR31_CAUSE_DIVBYZERO)
            put(1.0 / a if a != 0.0 else float("inf"))
        elif funct == 0x16:  # RSQRT
            if a < 0: cpu._set_fp_cause(FCR31_CAUSE_INVALID); put(float("nan"))
            elif a == 0.0: cpu._set_fp_cause(FCR31_CAUSE_DIVBYZERO); put(float("inf"))
            else: put(1.0 / math.sqrt(a))
        elif funct == 0x20:  # CVT.S
            cpu.fset32(fd, f32_to_bits(a))
        elif funct == 0x21:  # CVT.D
            cpu.fset64(fd, f64_to_bits(a))
        elif funct == 0x24:  # CVT.W (current rounding mode)
            cpu.fset32(fd, _fp_to_int(a, rm, 32))
        elif funct == 0x25:  # CVT.L
            cpu.fset64(fd, _fp_to_int(a, rm, 64))
        elif 0x0C <= funct <= 0x0F:  # ROUND/TRUNC/CEIL/FLOOR.W
            cpu.fset32(fd, _fp_to_int(a, funct - 0x0C, 32))
        elif 0x08 <= funct <= 0x0B:  # ROUND/TRUNC/CEIL/FLOOR.L
            cpu.fset64(fd, _fp_to_int(a, funct - 0x08, 64))
        elif funct >= 0x30:
            if _fp_cmp(a, b, funct): cpu.fcr31 |= (1 << FCR31_COND_BIT)
            else: cpu.fcr31 &= ~(1 << FCR31_COND_BIT)
    elif fmt_id == _ID_FPU_W:
        wi = sign32(cpu.fget32(fs))
        if funct == 0x20: cpu.fset32(fd, f32_to_bits(float(wi)))      # CVT.S.W
        elif funct == 0x21: cpu.fset64(fd, f64_to_bits(float(wi)))    # CVT.D.W
    elif fmt_id == _ID_FPU_L:
        li = sign64(cpu.fget64(fs))
        if funct == 0x20: cpu.fset32(fd, f32_to_bits(float(li)))      # CVT.S.L
        elif funct == 0x21: cpu.fset64(fd, f64_to_bits(float(li)))    # CVT.D.L


# ── UltraHLE OP_PATCH / OP_GROUP (primary 0x1C / 0x1D) ──
# UltraHLE rewrote libultra OS entry points to PATCH(id)=(0x1C<<26)|id.
# Encoding matches EmulatorArchive/ultrahle ULTRA.H: OP_PATCH=28, OP_GROUP=29.
ULTRAHLE_OP_PATCH = 0x1C
ULTRAHLE_OP_GROUP = 0x1D
ULTRAHLE_OS_SEG = 0x03FF0000  # UltraHLE thread-return page (PATCH 28)
ULTRAHLE_THREAD_RA = 0x03FF0000
ULTRAHLE_MQ_MAGIC = 0xFCFC1234
ULTRAHLE_MAX_THREAD = 16
ULTRAHLE_MAX_QUEUE = 128
def make_ultrahle_patch(patch_id: int) -> int:
    return u32((ULTRAHLE_OP_PATCH << 26) | (patch_id & 0xFFFF))

# GPR aliases (N64 o32)
_UH_V0, _UH_V1, _UH_A0, _UH_A1, _UH_A2, _UH_A3, _UH_SP, _UH_RA = 2, 3, 4, 5, 6, 7, 29, 31
OS_EVENT_SW1=0; OS_EVENT_SW2=1; OS_EVENT_CART=2; OS_EVENT_COUNTER=3
OS_EVENT_SP=4; OS_EVENT_SI=5; OS_EVENT_AI=6; OS_EVENT_VI=7; OS_EVENT_PI=8; OS_EVENT_DP=9
OS_EVENT_PRENMI=14; OS_EVENT_RETRACE=15  # UltraHLE uses RETRACE for osViSetEvent
OS_MESG_NOBLOCK=0; OS_MESG_BLOCK=1


class UltraHleOs:
    """UltraHLE os.c — threads, mesg queues, events, timers (PATCH-backed)."""
    __slots__ = (
        "core", "queues", "queue_by_addr", "queuenum",
        "event_mq", "event_msg", "fb_current", "fb_next",
        "threads", "thread_by_addr", "current_thread", "threadnum",
        "timers", "sptaskload", "time_lo", "time_hi",
        "cont_status", "cont_pad", "ai_freq", "ai_buf", "ai_len",
        "ismario", "iszelda", "bootloader", "block_pc", "pending_switch", "preempt_tid",
    )

    def __init__(self, core: "ACsN64Core"):
        self.core = core
        self.reset()

    def reset(self):
        self.queues: Dict[int, Dict[str, Any]] = {}
        self.queue_by_addr: Dict[int, int] = {}
        self.queuenum = 1
        self.event_mq: Dict[int, int] = {}
        self.event_msg: Dict[int, int] = {}
        self.fb_current = 0
        self.fb_next = 0
        self.threads: Dict[int, Dict[str, Any]] = {}
        self.thread_by_addr: Dict[int, int] = {}
        self.current_thread = 0
        self.threadnum = 1
        self.timers: Dict[int, Dict[str, Any]] = {}
        self.sptaskload = False
        self.time_lo = 0
        self.time_hi = 0
        self.cont_status = 0x0500
        self.cont_pad = 0
        self.ai_freq = 32000
        self.ai_buf = 0
        self.ai_len = 0
        self.ismario = 0
        self.iszelda = 0
        self.bootloader = 0
        self.block_pc = 0
        self.pending_switch = 0
        self.preempt_tid = 0
        # Boot context as thread 0 (idle/boot)
        self.threads[0] = {
            "id": 0, "memaddr": 0, "active": 1, "ready": 1, "pri": 0,
            "recvblock": 0, "sendblock": 0,
            "pc": 0, "next_pc": 4, "gpr": [0] * 32, "hi": 0, "lo": 0,
        }

    # compat alias used by older helpers
    @property
    def mq(self):
        return self.queue_by_addr

    @property
    def running_thread(self):
        return self.current_thread

    @running_thread.setter
    def running_thread(self, v):
        self.current_thread = v

    def _bus(self):
        return self.core.bus

    def _rd32(self, addr: int) -> int:
        return self._bus().read_u32(u32(addr))

    def _wr32(self, addr: int, val: int):
        self._bus().write_u32(u32(addr), u32(val))

    def _sp_arg(self, g, n: int) -> int:
        return self._rd32(u32(g[_UH_SP] + 0x10 + n * 4))

    def install_patch(self, vaddr: int, patch_id: int):
        self._wr32(vaddr, make_ultrahle_patch(patch_id))

    def _save_thread_cpu(self, tid: int):
        cpu = self.core.cpu
        t = self.threads.get(tid)
        if t is None:
            return
        t["pc"] = u32(cpu.pc)
        t["next_pc"] = u32(cpu.next_pc)
        t["gpr"] = list(cpu.gpr)
        t["hi"] = cpu.hi
        t["lo"] = cpu.lo

    def _load_thread_cpu(self, tid: int):
        cpu = self.core.cpu
        t = self.threads[tid]
        cpu.gpr = list(t["gpr"])
        cpu.gpr[0] = 0
        cpu.hi = t.get("hi", 0)
        cpu.lo = t.get("lo", 0)
        cpu.pc = u32(t["pc"])
        cpu.next_pc = u32(t["next_pc"])
        self.current_thread = tid

    def _find_ready_thread(self, prefer: int = 0) -> Optional[int]:
        best = None
        best_pri = -1
        start = prefer if prefer else self.current_thread
        for i in range(ULTRAHLE_MAX_THREAD * 2):
            tid = (start + 1 + i) & (ULTRAHLE_MAX_THREAD - 1)
            t = self.threads.get(tid)
            if not t or not t.get("ready"):
                continue
            pri = int(t.get("pri", 0))
            if pri > best_pri:
                best = tid
                best_pri = pri
        return best

    def switch_to(self, tid: int):
        if tid == self.current_thread:
            return
        if tid not in self.threads:
            return
        self._save_thread_cpu(self.current_thread)
        self._load_thread_cpu(tid)

    def schedule(self, prefer: int = 0) -> bool:
        """UltraHLE forcetaskswitch / os_switchcheck (simplified).

        Switch only when the current thread is not ready, or when another ready
        thread has strictly higher priority (preempt). Never demote a running
        high-priority thread to idle/boot just because schedule() was called.
        """
        cur = self.threads.get(self.current_thread)
        cur_ready = bool(cur is not None and cur.get("ready"))
        cur_pri = int(cur.get("pri", -1)) if cur_ready else -1
        t = self._find_ready_thread(prefer)
        pref_t = self.threads.get(prefer) if prefer else None
        if prefer and pref_t and pref_t.get("ready"):
            # Prefer started/unblocked thread when its priority wins or ties.
            if t is None or pref_t.get("pri", 0) >= self.threads.get(t, {}).get("pri", -1):
                t = prefer
        if t is not None and t != self.current_thread:
            t_pri = int(self.threads[t].get("pri", 0))
            if (not cur_ready) or t_pri > cur_pri:
                self.switch_to(t)
                return True
        return False

    def block_current(self, reason_q: int = 0, send: bool = False):
        """UltraHLE blocktask — mark not ready and switch away."""
        tid = self.current_thread
        t = self.threads.get(tid)
        if t is None:
            return
        t["ready"] = 0
        if send:
            t["sendblock"] = reason_q
        else:
            t["recvblock"] = reason_q
        # Rewind is handled by patch returning "block"; save after rewind via caller.
        self.schedule(0)

    def unblock_waiters(self, qid: int, recv: bool = True):
        # Mark ready only. If the waiter outranks the current thread, request a
        # deferred preempt so _h_PATCH can switch AFTER restoring the sender's RA
        # (immediate schedule mid-PATCH would corrupt the woken thread's PC).
        for tid, t in self.threads.items():
            if recv and t.get("recvblock") == qid:
                t["recvblock"] = 0
                t["ready"] = 1
                self._request_preempt(tid)
                return
            if (not recv) and t.get("sendblock") == qid:
                t["sendblock"] = 0
                t["ready"] = 1
                self._request_preempt(tid)
                return

    def _request_preempt(self, tid: int):
        t = self.threads.get(tid)
        if t is None or not t.get("ready"):
            return
        cur = self.threads.get(self.current_thread)
        cur_pri = int(cur.get("pri", -1)) if cur is not None else -1
        if int(t.get("pri", 0)) > cur_pri:
            self.preempt_tid = tid

    def maybe_preempt(self) -> bool:
        """Switch to a pending higher-priority thread if one was woken."""
        tid = self.preempt_tid
        self.preempt_tid = 0
        if tid and tid != self.current_thread:
            t = self.threads.get(tid)
            if t is not None and t.get("ready"):
                return self.schedule(tid)
        # Also pick any ready thread that outranks the current one.
        cur = self.threads.get(self.current_thread)
        cur_pri = int(cur.get("pri", -1)) if cur is not None else -1
        best = self._find_ready_thread()
        if best is not None and best != self.current_thread:
            if int(self.threads[best].get("pri", 0)) > cur_pri:
                return self.schedule(best)
        return False

    def yield_fair(self) -> bool:
        """Round-robin among ready non-idle threads so a mid-pri compute loop
        (e.g. SM64 audio) cannot starve lower-pri graphics for a whole frame."""
        cur = self.current_thread
        ready = [
            tid for tid, t in self.threads.items()
            if t.get("ready") and int(t.get("pri", 0)) > 0
        ]
        if len(ready) < 2:
            return False
        ready.sort()
        try:
            idx = ready.index(cur)
            nxt = ready[(idx + 1) % len(ready)]
        except ValueError:
            nxt = ready[0]
        if nxt != cur:
            self.switch_to(nxt)
            return True
        return False

    # ── queues (UltraHLE layout: id @+0, magic @+4, valid @+8, max @+16) ──
    def _queue_to_mem(self, qid: int):
        q = self.queues[qid]
        mq = q["memaddr"]
        self._wr32(mq + 0x00, qid)
        self._wr32(mq + 0x04, ULTRAHLE_MQ_MAGIC)
        self._wr32(mq + 0x08, q["num"])
        self._wr32(mq + 0x10, q["size"])

    def os_create_mesg_queue(self, mq: int, msg: int, count: int):
        mq = u32(mq); msg = u32(msg); count = max(0, sign32(count))
        # Reuse dead id or allocate
        qid = self.queue_by_addr.get(mq)
        if not qid:
            qid = self.queuenum
            self.queuenum = min(self.queuenum + 1, ULTRAHLE_MAX_QUEUE - 1)
            if qid <= 0:
                qid = 1
        self.queues[qid] = {
            "memaddr": mq, "msg": msg, "size": max(1, count), "num": 0, "pos": 0,
            "data": [0] * max(1, count),
        }
        self.queue_by_addr[mq] = qid
        self._queue_to_mem(qid)

    def _qid_from_mq(self, mq: int) -> int:
        mq = u32(mq)
        qid = self._rd32(mq)
        if qid in self.queues and self.queues[qid]["memaddr"] == mq:
            return qid
        if mq in self.queue_by_addr:
            return self.queue_by_addr[mq]
        # Uninitialized: treat as empty create
        return 0

    def os_send_mesg(self, mq: int, mesg: int, block: int) -> int:
        qid = self._qid_from_mq(mq)
        if not qid or qid not in self.queues:
            return 0
        q = self.queues[qid]
        if q["num"] >= q["size"]:
            if block == OS_MESG_NOBLOCK or block == -1:
                # Drop oldest so VI/SP event streams never permanently stall.
                if q["size"] > 0:
                    q["num"] -= 1
                else:
                    return -1
            else:
                self.block_pc = 1
                cur = self.threads.get(self.current_thread)
                if cur is not None:
                    cur["sendblock"] = qid
                return 1
        q["data"][q["pos"]] = u32(mesg)
        q["num"] += 1
        q["pos"] = (q["pos"] + 1) % q["size"]
        self._queue_to_mem(qid)
        self.unblock_waiters(qid, recv=True)
        return 0

    def os_recv_mesg(self, mq: int, msg_ptr: int, block: int) -> int:
        qid = self._qid_from_mq(mq)
        if not qid or qid not in self.queues:
            if block == OS_MESG_NOBLOCK:
                return -1
            self.block_pc = 1
            return 1
        q = self.queues[qid]
        if q["num"] <= 0:
            if block == OS_MESG_NOBLOCK:
                return -1
            self.block_pc = 1
            cur = self.threads.get(self.current_thread)
            if cur is not None:
                cur["recvblock"] = qid
            return 1
        pos = q["pos"] - q["num"]
        if pos < 0:
            pos += q["size"]
        mesg = q["data"][pos]
        q["num"] -= 1
        self._queue_to_mem(qid)
        if msg_ptr:
            self._wr32(msg_ptr, u32(mesg))
        self.unblock_waiters(qid, recv=False)
        return 0

    def os_set_event_mesg(self, event: int, mq: int, mesg: int):
        event &= 0xFF
        self.event_mq[event] = u32(mq)
        self.event_msg[event] = u32(mesg)

    def os_event(self, event: int):
        mq = self.event_mq.get(event)
        if mq is not None:
            self.os_send_mesg(mq, self.event_msg.get(event, 0), OS_MESG_NOBLOCK)

    def tick_time(self, cycles: int = 1):
        self.time_lo = u32(self.time_lo + cycles)
        if self.time_lo < (cycles & MASK_32):
            self.time_hi = u32(self.time_hi + 1)
        self._fire_timers(u32(self.core.cpu.cp0[CP0_COUNT]))

    def _fire_timers(self, count: int):
        """Deliver osSetTimer messages when COUNT reaches expiry."""
        count = u32(count)
        for t in self.timers.values():
            if not t.get("active"):
                continue
            expire = u32(t.get("expire", 0))
            # Not expired yet if (count - expire) is still a large unsigned (count < expire).
            if u32(count - expire) > 0x7FFFFFFF:
                continue
            mq = t.get("mq")
            if mq:
                self.os_send_mesg(mq, t.get("msg", 0), OS_MESG_NOBLOCK)
            iv = u32(t.get("interval", 0))
            if iv:
                t["expire"] = u32(count + iv)
            else:
                t["active"] = False

    def virt_to_phys(self, addr: int) -> int:
        return self._bus().v_to_p(u32(addr)) & 0x1FFFFFFF

    def phys_to_virt(self, addr: int) -> int:
        return u32(0x80000000 | (u32(addr) & 0x1FFFFFFF))

    def create_thread(self, m_thread: int, tid: int, entry: int, arg: int, stack: int, pri: int):
        m_thread = u32(m_thread)
        tid = u32(tid) & 0xFF
        if tid <= 0 or tid >= ULTRAHLE_MAX_THREAD or (tid in self.threads and self.threads[tid].get("active")):
            for i in range(1, ULTRAHLE_MAX_THREAD):
                if i not in self.threads or not self.threads[i].get("active"):
                    tid = i
                    break
        gpr = [0] * 32
        gpr[4] = u64(arg)
        gpr[29] = u64(u32(stack) - 8)
        gpr[31] = u64(ULTRAHLE_THREAD_RA)
        self.threads[tid] = {
            "id": tid, "memaddr": m_thread, "active": 1, "ready": 0,
            "pri": int(pri) * 10, "recvblock": 0, "sendblock": 0,
            "pc": u32(entry), "next_pc": u32(entry + 4),
            "gpr": gpr, "hi": 0, "lo": 0,
        }
        self.thread_by_addr[m_thread] = tid
        self._wr32(m_thread, tid)
        if tid >= self.threadnum:
            self.threadnum = tid + 1

    def start_thread(self, m_thread: int):
        m_thread = u32(m_thread)
        tid = self._rd32(m_thread)
        if tid not in self.threads:
            tid = self.thread_by_addr.get(m_thread, tid)
        t = self.threads.get(tid)
        if t is None:
            return
        t["ready"] = 1
        # Save current so it resumes at RA (after this PATCH returns).
        cpu = self.core.cpu
        cur = self.threads.get(self.current_thread)
        ra = u32(cpu.gpr[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        if cur is not None:
            cur["pc"] = ra
            cur["next_pc"] = u32(ra + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        self.pending_switch = tid
        # Prefer the started thread if its priority wins (do not re-save current).
        self.schedule(tid)

    def stop_current_thread(self):
        tid = self.current_thread
        t = self.threads.get(tid)
        if t is not None:
            t["active"] = 0
            t["ready"] = 0
        self.schedule(0)


# Patch routines — indices match UltraHLE PATCH.C patchtable[]
def _uh_skip(hle, cpu, g): pass
def _uh_osskip(hle, cpu, g): pass
def _uh_osskip0(hle, cpu, g): g[_UH_V0] = 0
def _uh_dabort(hle, cpu, g): pass

def _uh_ddivu(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    if b == 0: r = 0
    else: r = a // b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_dmultu(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    r = a * b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_drem(hle, cpu, g):
    a = (u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32)
    b = (u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32)
    r = 0 if b == 0 else a % b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_ddiv(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    b = sign64((u64(g[_UH_A2]) << 32) | u64(g[_UH_A3] & MASK_32))
    r = 0 if b == 0 else a // b
    g[_UH_V0] = u64(r >> 32); g[_UH_V1] = u64(r & MASK_32)

def _uh_osCreateThread(hle, cpu, g):
    hle.create_thread(
        u32(g[_UH_A0]), u32(g[_UH_A1]), u32(g[_UH_A2]), u32(g[_UH_A3]),
        hle._sp_arg(g, 0), hle._sp_arg(g, 1),
    )

def _uh_osStartThread(hle, cpu, g):
    hle.start_thread(u32(g[_UH_A0]))
    return "switched"

def _uh_osStopCurrentThread(hle, cpu, g):
    hle.stop_current_thread()
    return "switched"

def _uh_osSetThreadPri(hle, cpu, g):
    m_thr = u32(g[_UH_A0])
    pri = u32(g[_UH_A1])
    tid = hle.current_thread if m_thr == 0 else hle._rd32(m_thr)
    t = hle.threads.get(tid)
    if t is not None:
        t["pri"] = int(pri) * 10
        # Resume caller at RA after any forced switch (not mid-PATCH).
        ra = u32(g[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        hle.schedule(tid)
        return "switched"

def _uh_osPiStartDma(hle, cpu, g):
    # A0=mb, A1=pri, A2=direction, A3=devAddr; stack: vAddr, nBytes, mq
    direction = u32(g[_UH_A2])
    dev = u32(g[_UH_A3])
    vaddr = hle._sp_arg(g, 0)
    nbytes = hle._sp_arg(g, 1)
    mq = hle._sp_arg(g, 2)
    bus = hle._bus()
    # cart offset is often a raw cart address; accept both 0x1xxx_xxxx and bare offsets
    cart = u32(dev)
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(vaddr) & 0x00FFFFFF
    bus.regs[PI_CART_ADDR] = cart
    if direction == 0:  # cart -> rdram
        bus.regs[PI_WR_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_RD_LEN] = 0
        hle.core.trigger_pi_dma()
    else:
        bus.regs[PI_RD_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_WR_LEN] = 0
        hle.core.trigger_pi_dma()
    # UltraHLE: notify requester queue immediately, then PI event.
    if mq:
        hle.os_send_mesg(mq, 0, -1)
    hle.os_event(OS_EVENT_PI)
    g[_UH_V0] = 0

def _uh_osEPiStartDma(hle, cpu, g):
    # A0=OSPiHandle*, A1=OSIoMesg* — DMA from mesg fields, notify retQueue.
    mb = u32(g[_UH_A1])
    if not mb:
        g[_UH_V0] = -1
        return
    mq = hle._rd32(mb + 4)
    vaddr = hle._rd32(mb + 8)
    dev = hle._rd32(mb + 12)
    nbytes = hle._rd32(mb + 16)
    # OS_READ=0 (cart→RDRAM), OS_WRITE=1
    direction = hle._rd32(mb) & 0xFF
    bus = hle._bus()
    cart = u32(dev)
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(vaddr) & 0x00FFFFFF
    bus.regs[PI_CART_ADDR] = cart
    if direction == 0:
        bus.regs[PI_WR_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_RD_LEN] = 0
    else:
        bus.regs[PI_RD_LEN] = max(0, int(nbytes) - 1)
        bus.regs[PI_WR_LEN] = 0
    hle.core.trigger_pi_dma()
    if mq:
        hle.os_send_mesg(mq, mb, -1)
    hle.os_event(OS_EVENT_PI)
    g[_UH_V0] = 0

def _uh_osCreateMesgQueue(hle, cpu, g):
    hle.os_create_mesg_queue(g[_UH_A0], g[_UH_A1], g[_UH_A2])

def _uh_osRecvMesg(hle, cpu, g):
    hle.block_pc = 0
    rc = hle.os_recv_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2])
    if hle.block_pc:
        # UltraHLE blocktask: mark not-ready FIRST, then yield to another thread.
        # Do NOT inject os_event here — that can fill the wait queue and clear
        # recvblock, after which setting ready=0 leaves the thread wedged.
        cur = hle.threads.get(hle.current_thread)
        patch_pc = u32(getattr(cpu, "_patch_pc", cpu.pc))
        # Rewind onto PATCH before schedule/_save so we don't resume mid-native body.
        cpu.pc = patch_pc
        cpu.next_pc = u32(patch_pc + 4)
        if cur is not None:
            cur["ready"] = 0
            cur["pc"] = patch_pc
            cur["next_pc"] = u32(patch_pc + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        g[_UH_V0] = 0
        cpu.gpr[_UH_V0] = 0
        cpu.cp0[CP0_COUNT] = u32(cpu.cp0[CP0_COUNT] + 64)
        switched = hle.schedule(0)
        if switched:
            return "switched"
        return "block"
    g[_UH_V0] = sx32_to_64(rc)
    return None

def _uh_osSendMesg(hle, cpu, g):
    g[_UH_V0] = sx32_to_64(hle.os_send_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2]))

def _uh_osSetEventMessage(hle, cpu, g):
    hle.os_set_event_mesg(g[_UH_A0], g[_UH_A1], g[_UH_A2])

def _uh_osViSetEvent(hle, cpu, g):
    # UltraHLE maps this to OS_EVENT_RETRACE only (sync.c). Binding VI as well
    # double-posts on titles that share a size-1 mq with DMA/audio.
    hle.os_set_event_mesg(OS_EVENT_RETRACE, g[_UH_A0], g[_UH_A1])

def _uh_osGetTime(hle, cpu, g):
    hle.tick_time(cpu.cp0[CP0_COUNT] & MASK_32)
    g[_UH_V0] = u64(hle.time_hi)
    g[_UH_V1] = u64(hle.time_lo)

def _uh_osGetCount(hle, cpu, g):
    g[_UH_V0] = sx32_to_64(cpu.cp0[CP0_COUNT])

def _uh_osViGetCurrentFrameBuffer(hle, cpu, g):
    g[_UH_V0] = u64(hle.fb_current or hle._bus().regs.get(VI_ORIGIN, 0))

def _uh_osViSwapBuffer(hle, cpu, g):
    hle.fb_next = u32(g[_UH_A0])
    hle.fb_current = hle.fb_next
    # VI_ORIGIN is a physical DRAM address (24-bit); keep virt in fb_current for OS.
    hle._bus().regs[VI_ORIGIN] = hle.virt_to_phys(hle.fb_current) & 0x00FFFFFF
    hle.core._vi_origin_set = True
    hle.core.render_vi()
    # Real osViSwapBuffer does not post a mesg; VI/RETRACE interrupt does.

def _uh_osVirtualToPhysical(hle, cpu, g):
    g[_UH_V0] = u64(hle.virt_to_phys(g[_UH_A0]))

def _uh_osPhysicalToVirtual(hle, cpu, g):
    g[_UH_V0] = u64(hle.phys_to_virt(g[_UH_A0]))

def _uh_osSpTaskStartGo(hle, cpu, g):
    task = u32(g[_UH_A0])
    if not hle.sptaskload:
        if task:
            ttype = hle._rd32(task)
            put_be32(hle.core.rsp_dmem, 0xFC0, ttype)
            hle.core.last_os_task = task
        hle.core.process_rsp()
    elif task:
        hle.core.last_os_task = task
    hle.sptaskload = False
    # UltraHLE retires RSP/RDP immediately — notify event subscribers.
    hle.os_event(OS_EVENT_SP)
    hle.os_event(OS_EVENT_DP)

def _uh_osSpTaskLoad(hle, cpu, g):
    task = u32(g[_UH_A0])
    if task:
        ttype = hle._rd32(task)
        put_be32(hle.core.rsp_dmem, 0xFC0, ttype)
        hle.core.last_os_task = task
    hle.core.process_rsp()
    hle.sptaskload = True
    # Completion events fired by osSpTaskStartGo.

def _uh_osSpTaskYield(hle, cpu, g): g[_UH_V0] = 0
def _uh_osSpTaskYielded(hle, cpu, g): g[_UH_V0] = 0

def _uh_osMapTLB(hle, cpu, g):
    # A0=index, A1=pmask, A2=vaddr, A3=evenpaddr; stack: oddpaddr, asid
    idx = u32(g[_UH_A0]) & 0x1F
    pmask = u32(g[_UH_A1])
    vaddr = u32(g[_UH_A2])
    even_p = u32(g[_UH_A3])
    odd_p = hle._sp_arg(g, 0)
    asid = hle._sp_arg(g, 1) & 0xFF
    cpu.cp0[CP0_INDEX] = idx
    cpu.cp0[CP0_PAGEMASK] = pmask
    cpu.cp0[CP0_ENTRYHI] = (vaddr & 0xFFFFE000) | asid
    cpu.cp0[CP0_ENTRYLO0] = ((even_p >> 12) << 6) | 0x06  # V|D
    cpu.cp0[CP0_ENTRYLO1] = ((odd_p >> 12) << 6) | 0x06
    cpu._write_tlb_entry(idx)

def _uh_osContInit(hle, cpu, g):
    # Write status pattern into statusdata if provided
    status = u32(g[_UH_A1])
    if status:
        hle._wr32(status, 0x05000200)
    g[_UH_V0] = 0

def _uh_osContStartReadData(hle, cpu, g):
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0

def _uh_osContGetReadData(hle, cpu, g):
    pad = u32(g[_UH_A0])
    if not pad:
        return
    bus = hle._bus()
    # OSContPad: u16 button, s8 stick_x, s8 stick_y, u8 errno (6 bytes × 4).
    for i in range(4):
        base = pad + i * 6
        btn = (hle.cont_pad & 0xFFFF) if i == 0 else 0
        bus.write_u16(base, btn)
        bus.write_u8(base + 2, 0)
        bus.write_u8(base + 3, 0)
        bus.write_u8(base + 4, 0)

def _uh_osContStartQuery(hle, cpu, g):
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0

def _uh_osContGetQuery(hle, cpu, g):
    status = u32(g[_UH_A0])
    if status:
        hle._wr32(status, 0x05000200)

def _uh_osAiSetNextBuffer(hle, cpu, g):
    hle.ai_buf = u32(g[_UH_A0]); hle.ai_len = u32(g[_UH_A1])
    hle._bus().regs[AI_DRAM_ADDR] = hle.ai_buf & 0x00FFFFFF
    hle._bus().regs[AI_LEN] = hle.ai_len
    hle.core.process_audio()
    # Audio threads block on AI completion — post the event so commercial titles continue.
    hle.os_event(OS_EVENT_AI)
    g[_UH_V0] = 0

def _uh_osAiGetLength(hle, cpu, g):
    g[_UH_V0] = u64(hle._bus().regs.get(AI_LEN, 0))

def _uh_osAiSetFrequency(hle, cpu, g):
    hle.ai_freq = u32(g[_UH_A0]) or 32000
    g[_UH_V0] = u64(hle.ai_freq)

def _uh_osSetTimer(hle, cpu, g):
    # osSetTimer(OSTimer*, OSTime countdown, OSTime interval, OSMesgQueue*, OSMesg)
    # o32: A0=timer, A2:A3=countdown, stack=interval(hi,lo), mq, msg.
    timer = u32(g[_UH_A0])
    countdown = u32(g[_UH_A3])  # low half is enough for HLE pacing
    interval = u32(hle._sp_arg(g, 1))
    mq = hle._sp_arg(g, 2)
    msg = hle._sp_arg(g, 3)
    now = u32(cpu.cp0[CP0_COUNT])
    delay = countdown if countdown else 1
    hle.timers[timer] = {
        "active": True,
        "expire": u32(now + delay),
        "interval": interval,
        "mq": mq,
        "msg": msg,
    }
    g[_UH_V0] = 0

def _uh_osStopTimer(hle, cpu, g):
    timer = u32(g[_UH_A0])
    if timer in hle.timers:
        hle.timers[timer]["active"] = False

def _uh_sinf(hle, cpu, g):
    x = bits_to_f32(cpu.fpr[12] & MASK_32)
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(math.sin(x)))

def _uh_cosf(hle, cpu, g):
    x = bits_to_f32(cpu.fpr[12] & MASK_32)
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(math.cos(x)))

def _uh_osInvalICache(hle, cpu, g): pass

def _uh_readdma(hle, cpu, g):
    # Zelda-style cart→RDRAM helper: A0=cart, A1=dram, A2=nbytes
    bus = hle._bus()
    cart = u32(g[_UH_A0])
    if cart < 0x10000000:
        cart = u32(0x10000000 + (cart & 0x0FFFFFFF))
    bus.regs[PI_CART_ADDR] = cart
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(g[_UH_A1]) & 0x00FFFFFF
    bus.regs[PI_WR_LEN] = max(0, u32(g[_UH_A2]) - 1)
    bus.regs[PI_RD_LEN] = 0
    hle.core.trigger_pi_dma()
    hle.os_event(OS_EVENT_PI)

def _uh_readdma2(hle, cpu, g):
    # Patched to osPiStartDma(0,0,0,A0,A1,A2,0)
    bus = hle._bus()
    bus.regs[PI_CART_ADDR] = u32(g[_UH_A0])
    bus.regs[PI_DRAM_ADDR] = hle.virt_to_phys(g[_UH_A1]) & 0x00FFFFFF
    bus.regs[PI_WR_LEN] = max(0, u32(g[_UH_A2]) - 1)
    hle.core.trigger_pi_dma()

def _uh_zeldacont(hle, cpu, g): hle.os_event(OS_EVENT_SI)
def _uh_zeldagrabscreen(hle, cpu, g): pass
def _uh_banjojalr(hle, cpu, g):
    # Fall through to next instruction (UltraHLE branches to pc+4)
    cpu.pc = u32(cpu.pc)  # already at delay/next after execute preamble
    # Keep sequential fetch: undo RA return by staying at next_pc path.
    # Caller already set pc=RA; Banjo patch instead continues. Restore:
    pass  # handled specially in _h_PATCH

def _uh_long2double(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    cpu.fpr[0] = f64_to_bits(float(a))

def _uh_long2single(hle, cpu, g):
    a = sign64((u64(g[_UH_A0]) << 32) | u64(g[_UH_A1] & MASK_32))
    cpu.fpr[0] = u64((cpu.fpr[0] & 0xFFFFFFFF00000000) | f32_to_bits(float(a)))

def _uh_double2long(hle, cpu, g):
    d = bits_to_f64(cpu.fpr[12])
    a = int(d) if math.isfinite(d) else 0
    g[_UH_V1] = u64(a & MASK_32); g[_UH_V0] = u64((a >> 32) & MASK_32)

def _uh_single2long(hle, cpu, g):
    f = bits_to_f32(cpu.fpr[12] & MASK_32)
    a = int(f) if math.isfinite(f) else 0
    g[_UH_V1] = u64(a & MASK_32); g[_UH_V0] = u64((a >> 32) & MASK_32)

def _uh_golden1(hle, cpu, g):
    x = random.randint(0, 0xFFFFFFFF)
    x = u32((x << 8) | (x >> 24))
    g[_UH_V0] = sx32_to_64(x)

def _uh_createvimanager(hle, cpu, g):
    # A0 is priority (e.g. SM64 passes 0xFE), not a mesg queue. Real libultra
    # spins up a VI manager thread; with HLE osViSetEvent we already deliver
    # retrace msgs, so this is a no-op (do not overwrite event MQ with priority).
    g[_UH_V0] = 0

def _uh_memcpy(hle, cpu, g):
    dst, src, count = u32(g[_UH_A0]), u32(g[_UH_A1]), u32(g[_UH_A2]) >> 2
    bus = hle._bus()
    for _ in range(count):
        bus.write_u32(dst, bus.read_u32(src))
        dst = u32(dst + 4); src = u32(src + 4)

def _uh_osEepromProbe(hle, cpu, g):
    # osEepromProbe(OSMesgQueue*) → EEPROM_TYPE_4K/16K or 0
    sm = hle.core.save_mgr
    typ = sm.eeprom_probe()
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = typ

def _uh_osEepromRead(hle, cpu, g):
    # osEepromRead(mq, address, buffer) — 8 bytes at block `address`
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    tmp = bytearray(EEPROM_BLOCK)
    rc = sm.eeprom_read_block(block, tmp)
    if rc == 0 and buf:
        bus = hle._bus()
        for i in range(EEPROM_BLOCK):
            bus.write_u8(u32(buf + i), tmp[i])
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromWrite(hle, cpu, g):
    # osEepromWrite(mq, address, buffer)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    tmp = bytearray(EEPROM_BLOCK)
    if buf:
        bus = hle._bus()
        for i in range(EEPROM_BLOCK):
            tmp[i] = bus.read_u8(u32(buf + i)) & 0xFF
    rc = sm.eeprom_write_block(block, tmp)
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromLongRead(hle, cpu, g):
    # osEepromLongRead(mq, address, buffer, nbytes) — nbytes in A3 (o32)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    nbytes = u32(g[_UH_A3])
    rc = sm.eeprom_long_read(block, nbytes, hle._bus(), buf) if buf else -1
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

def _uh_osEepromLongWrite(hle, cpu, g):
    # osEepromLongWrite(mq, address, buffer, nbytes) — nbytes in A3 (o32)
    sm = hle.core.save_mgr
    block = u32(g[_UH_A1]) & 0xFF
    buf = u32(g[_UH_A2])
    nbytes = u32(g[_UH_A3])
    rc = sm.eeprom_long_write(block, nbytes, hle._bus(), buf) if buf else -1
    hle.os_event(OS_EVENT_SI)
    g[_UH_V0] = 0 if rc == 0 else -1

# Index-aligned with UltraHLE PATCH.C patchtable[] (+ cathle EEPROM 57..61)
ULTRAHLE_PATCH_TABLE: Dict[int, Callable] = {
    1: _uh_skip, 2: _uh_osskip, 3: _uh_ddivu, 4: _uh_dmultu,
    5: _uh_drem, 6: _uh_ddiv, 7: _uh_drem, 8: _uh_osskip0, 9: _uh_dabort,
    10: _uh_osCreateThread, 11: _uh_osStartThread, 12: _uh_osPiStartDma,
    13: _uh_osCreateMesgQueue, 14: _uh_osRecvMesg, 15: _uh_osSendMesg,
    16: _uh_osSetEventMessage, 17: _uh_osViSetEvent, 18: _uh_osSetThreadPri,
    19: _uh_osGetTime, 20: _uh_osViGetCurrentFrameBuffer, 21: _uh_osVirtualToPhysical,
    22: _uh_osSpTaskStartGo, 23: _uh_osViSwapBuffer, 24: _uh_osMapTLB,
    25: _uh_osContInit, 26: _uh_osContStartReadData, 27: _uh_osContGetReadData,
    28: _uh_osStopCurrentThread, 29: _uh_osPhysicalToVirtual,
    30: _uh_osAiSetNextBuffer, 31: _uh_osAiGetLength, 32: _uh_osAiSetFrequency,
    33: _uh_osSetTimer, 34: _uh_osStopTimer, 35: _uh_sinf, 36: _uh_cosf,
    37: _uh_osEPiStartDma, 38: _uh_osInvalICache, 39: _uh_osSpTaskLoad,
    40: _uh_readdma, 41: _uh_readdma2, 42: _uh_osContStartQuery, 43: _uh_osContGetQuery,
    44: _uh_zeldacont, 45: _uh_zeldagrabscreen, 46: _uh_osSpTaskYield,
    47: _uh_osSpTaskYielded, 48: _uh_osGetCount, 49: _uh_banjojalr,
    50: _uh_long2double, 51: _uh_long2single, 52: _uh_double2long, 53: _uh_single2long,
    54: _uh_golden1, 55: _uh_createvimanager, 56: _uh_memcpy,
    57: _uh_osEepromProbe, 58: _uh_osEepromRead, 59: _uh_osEepromWrite,
    60: _uh_osEepromLongRead, 61: _uh_osEepromLongWrite,
}
ULTRAHLE_PATCH_NAMES = {
    1: "skip", 2: "osskip", 3: "__ull_div", 4: "__ll_mul", 5: "__ull_rem",
    6: "__ll_div", 7: "__ll_rem", 8: "osskip0", 9: "dabort",
    10: "osCreateThread", 11: "osStartThread", 12: "osPiStartDma",
    13: "osCreateMesgQueue", 14: "osRecvMesg", 15: "osSendMesg",
    16: "osSetEventMesg", 17: "osViSetEvent", 18: "osSetThreadPri",
    19: "osGetTime", 20: "osViGetCurrentFramebuffer", 21: "osVirtualToPhysical",
    22: "osSpTaskStartGo", 23: "osViSwapBuffer", 24: "osMapTLB",
    25: "osContInit", 26: "osContStartReadData", 27: "osContGetReadData",
    28: "osStopCurrentThread", 29: "osPhysicalToVirtual",
    30: "osAiSetNextBuffer", 31: "osAiGetLength", 32: "osAiSetFrequency",
    33: "osSetTimer", 34: "osStopTimer", 35: "sinf", 36: "cosf",
    37: "osEPiStartDma", 38: "osInvalICache", 39: "osSpTaskLoad",
    40: "readdma", 41: "readdma2", 42: "osContStartQuery", 43: "osContGetQuery",
    44: "zeldacont", 45: "zeldagrabscreen", 46: "osSpTaskYield",
    47: "osSpTaskYielded", 48: "osGetCount", 49: "banjojalr",
    50: "long2double", 51: "long2single", 52: "double2long", 53: "single2long",
    54: "golden1", 55: "createViManager", 56: "memcpy",
    57: "osEepromProbe", 58: "osEepromRead", 59: "osEepromWrite",
    60: "osEepromLongRead", 61: "osEepromLongWrite",
}


# AUTOGEN: UltraHLE oscall/ospatch/ini (emu-russia/UltraHLE)
ULTRAHLE_OSCALL: List[Tuple] = [
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40008200,1,'__osGetCause  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000B200,1,'__osGetCompare  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40006A00,1,'__osGetConfig  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000A200,48,'osGetCount #48'),
  ((0x44424442,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x44401200,1,'__osGetFpcCsr  #1'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40008A00,1,'__osGetSR #1'),
  ((0x40024002,0x30423042,0x3C083C08,0x25082508,0x8D098D09,0x24012401,0x01210121,0x31083108),0x000028AA,0x44E69EF4,2,'osGetIntMask  #2'),
  ((0x40024002,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4000BA00,1,'__osGetTLBASID  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x4284D1C5,1,'__osGetTLBHi  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x428491C5,1,'__osGetTLBLo0  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x428499C5,1,'__osGetTLBLo1  #1'),
  ((0x40844084,0x00000000,0x42004200,0x00000000,0x00000000,0x00000000,0x40024002,0x03E003E0),0x00000000,0x4284A9C5,1,'__osGetTLBPageMask  #1'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00003A15,0x86C122C7,1,'osInvalDCache #1'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00001A15,0xFCC122C7,38,'osInvalICache #38'),
  ((0x40084008,0x24012401,0x01010101,0x40894089,0x31023102,0x00000000,0x03E003E0,0x00000000),0x00000012,0x0081B12C,1,'__osDisableInt #1'),
  ((0x40084008,0x01040104,0x40884088,0x00000000,0x00000000,0x03E003E0,0x00000000,0x00000000),0x00000000,0x06843070,1,'__osRestoreInt #1'),
  ((0x40084008,0x40844084,0x40854085,0x8FA98FA9,0x24012401,0x11211121,0x240C240C,0x240A240A),0x000035F0,0x5DB45780,24,'osMapTLB #24'),
  ((0x400C400C,0x31823182,0x3C083C08,0x25082508,0x8D0B8D0B,0x24012401,0x01610161,0x31083108),0x0000A8AA,0xAE358CFC,2,'osSetIntMask #2'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40868200,1,'__osSetCause  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086B200,1,'__osSetCompare #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40866A00,1,'__osSetConfig  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086A200,1,'__osSetCount  #1'),
  ((0x44424442,0x44C444C4,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00863700,1,'__osSetFpcCsr #1'),
  ((0x40844084,0x00000000,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x40845710,1,'__osSetSR  #1'),
  ((0x40844084,0x03E003E0,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x4086BA00,2,'osSetTLBASID  #2'),
  ((0x40084008,0x40844084,0x3C093C09,0x40894089,0x40804080,0x40804080,0x00000000,0x42004200),0x00000000,0x5AC36802,2,'osUnmapTLB  #2'),
  ((0x40084008,0x24092409,0x3C0A3C0A,0x408A408A,0x40804080,0x40804080,0x40894089,0x00000000),0x00000802,0x484FD806,2,'osUnmapTLBAll  #2'),
  ((0x18A018A0,0x00000000,0x240B240B,0x00AB00AB,0x10201020,0x00000000,0x00800080,0x00850085),0x00001A15,0xCCC122C7,2,'osWritebackDCache #2'),
  ((0x3C083C08,0x240A240A,0x010A010A,0x25292529,0xBD01BD01,0x01090109,0x14201420,0x25082508),0x000000CA,0x000E9F38,1,'osWritebackDCacheAll #1'),
  ((0x40084008,0x24092409,0x40894089,0x40804080,0x240A240A,0x3C093C09,0x40894089,0x3C093C09),0x00000812,0x4ACCA206,2,'osMapTLBRdb #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x8FAE8FAE,0xAFA2AFA2,0x8DCF8DCF,0x11E011E0),0x00001A81,0xEE2EC003,1,'__osAtomicDec  #1'),
  ((0x3C0E3C0E,0x3C0F3C0F,0x25CE25CE,0x25EF25EF,0xAC8EAC8E,0xAC8FAC8F,0xAC80AC80,0xAC80AC80),0x0000000C,0x001D0124,13,'osCreateMesgQueue #13'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0x8FAE8FAE,0x8FAF8FAF,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7),0x00000001,0x7B04BF73,10,'osCreateThread #10'),
  ((0x3C1A3C1A,0x275A275A,0x03400340,0x00000000,0x3C1A3C1A,0x275A275A,0xFF41FF41,0x401B401B),0x00000222,0x9EA512E4,1,'__osExceptionPreamble  #1'),
  ((0x3C1A3C1A,0x275A275A,0xFF41FF41,0x401B401B,0xAF5BAF5B,0x24012401,0x03610361,0x409B409B),0x00008022,0xFC437204,1,'__osException  #1'),
  ((0x3C0A3C0A,0x254A254A,0x01440144,0x8D498D49,0x03E003E0,0x11201120,0x00000000,0x8D2B8D2B),0x00008422,0xE07AFA48,0,'send_mesg'),
  ((0x3C013C01,0x01010101,0x00090009,0x240A240A,0x152A152A,0x00000000,0x8F5B8F5B,0x3C013C01),0x00004918,0x481AC224,0,'handle_CpU'),
  ((0x3C053C05,0x8CA58CA5,0x40084008,0x8CBB8CBB,0x35083508,0xACA8ACA8,0xFCB0FCB0,0xFCB1FCB1),0x00000012,0x73042C40,1,'__osEnqueueAndYield  #1'),
  ((0x8C988C98,0x8CAF8CAF,0x00800080,0x8F0E8F0E,0x01CF01CF,0x14201420,0x00000000,0x03000300),0x00000820,0x97A7BB74,1,'__osEnqueueThread  #1'),
  ((0x8C828C82,0x8C598C59,0x03E003E0,0xAC99AC99,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x0000579E,1,'__osPopThread  #1'),
  ((0x3C043C04,0x00000000,0x24842484,0x3C013C01,0xAC22AC22,0x24082408,0xA448A448,0x00400040),0x0000E434,0x08CBC6E4,1,'__osDispatchThread  #1'),
  ((0x00000000,0x00000000,0x00000000,0x00000000,0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2),0x00002010,0x12ECFAE7,1,'__osCleanupThread  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00003201,0x0E471BAF,2,'osDestroyThread  #2'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osGetActiveQueue  #1'),
  ((0x14801480,0x00000000,0x3C043C04,0x8C848C84,0x03E003E0,0x8C828C82,0x00000000,0x00000000),0x00000009,0x00E1B01D,2,'osGetThreadId  #2'),
  ((0x14801480,0x00000000,0x3C043C04,0x8C848C84,0x03E003E0,0x8C828C82,0x00000000,0x00000000),0x00000009,0x00F1B01D,2,'osGetThreadPri #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x00000000,0x00400040,0xAFA2AFA2,0x3C0F3C0F),0x00003101,0x126BB64B,19,'osGetTime #19'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0xAFB0AFB0,0xAFA0AFA0,0x00000000,0xAC2EAC2E),0x00004085,0x04AFB7CB,2,'osInitialize #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1,0x00000000,0xAFB0AFB0),0x00002001,0xD019FDBB,15,'osJamMesg #15'),
  ((0x3C013C01,0x03E003E0,0x00810081,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00B6EA0F,29,'osPhysicalToVirtual #29'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1,0x00000000,0xAFB0AFB0),0x00004801,0x2359FDBB,14,'osRecvMesg #14'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x8FAF8FAF,0x3C0E3C0E,0x8DCE8DCE),0x00004181,0xE0281BFB,1,'__osResetGlobalIntMask  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB2AFB2,0xAFB1AFB1,0x00000000),0x00004001,0x361417EF,15,'osSendMesg #15'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00000401,0x1AFB59BB,16,'osSetEventMesg #16'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x8FAF8FAF),0x00000841,0x00FF13FB,1,'__osSetGlobalIntMask  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FAF8FAF,0x8FAE8FAE),0x00004001,0x555B1ABB,1,'__osSetHWIntrRoutine  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040),0x00000901,0x4F2CCABB,18,'osSetThreadPri #18'),
  ((0xAFA4AFA4,0x8FAE8FAE,0xAFA5AFA5,0x3C013C01,0x8FAF8FAF,0xAC2EAC2E,0x3C013C01,0x03E003E0),0x00000120,0x000392F9,2,'osSetTime #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0xADC0ADC0,0x8FAF8FAF),0x00000001,0xB4E4AEBB,33,'osSetTimer #33'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x24012401),0x00009C81,0xCACB063B,11,'osStartThread #11'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB2AFB2,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE),0x00001A01,0x64071BAF,28,'osStopThread #28'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFB0AFB0,0x8DCF8DCF,0x15E015E0,0x00000000),0x00004341,0x396BBF2F,34,'osStopTimer #34'),
  ((0x00800080,0x8CC78CC7,0x27BD27BD,0x10E010E0,0x00000000,0x14E514E5,0x00000000,0x8CAE8CAE),0x0000912C,0xDA4BB5D7,1,'__osDequeueThread  #1'),
  ((0x3C013C01,0x240E240E,0x240F240F,0xAC2FAC2F,0xAC2EAC2E,0x3C013C01,0x3C183C18,0x8F188F18),0x0000A59E,0xF15FD19C,1,'__osTimerServicesInit  #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x8DCF8DCF,0x11EE11EE,0x00000000,0x3C183C18),0x00008526,0x782FB29C,1,'__osTimerInterrupt  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x00000000,0xAFA2AFA2,0x3C013C01),0x00008501,0x2F6DB8F3,1,'__osSetTimerIntr  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x3C0E3C0E,0x8DCE8DCE,0xAFA2AFA2,0x8FB88FB8),0x00002021,0x3915AAC3,1,'__osInsertTimer  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0x3C013C01,0xAFBFAFBF,0x01C101C1,0x14201420,0x3C013C01),0x00001A41,0x0E2098EF,21,'osVirtualToPhysical #21'),
  ((0x40084008,0x31093109,0x24012401,0x00810081,0x012A012A,0x40894089,0x00000000,0x00000000),0x00008006,0xBAC8B3C8,1,'__osProbeTLB #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0F3C0F,0x8DEF8DEF,0x240E240E,0x3C043C04),0x00000261,0x002F964B,2,'osYieldThread  #2'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osGetCurrFaultedThread  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040),0x00009901,0x922CC63B,1,'__osGetNextFaultedThread  #1'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C474E50,31,'osAiGetLength #31'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C4F4E50,2,'osAiGetStatus  #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x44844484,0x27BD27BD,0x448E448E,0x46804680,0x04810481,0x46804680),0x0000800A,0xC813D50F,32,'osAiSetFrequency #32'),
  ((0x27BD27BD,0x3C0F3C0F,0x91EF91EF,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0x11E011E0),0x0000A285,0x20D5C417,30,'osAiSetNextBuffer #30'),
  ((0x3C0E3C0E,0x8DC48DC4,0x3C013C01,0x27BD27BD,0x00810081,0x11E011E0,0x00000000,0x10001000),0x000009A8,0x3C8D5150,1,'__osAiDeviceBusy #1'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C4F4E10,2,'osDpGetStatus  #2'),
  ((0x3C0E3C0E,0x03E003E0,0xADC4ADC4,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C694E10,2,'osDpSetStatus  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0x00000000,0xAFB0AFB0,0x10401040),0x00000E81,0x6002E21B,2,'osDpSetNextBuffer  #2'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C334480,1,'__osDpDeviceBusy  #1'),
  ((0x3C0E3C0E,0x8DCF8DCF,0x3C183C18,0x3C083C08,0xAC8FAC8F,0x8F198F19,0x24842484,0x3C0A3C0A),0x00004C40,0xE27700EC,2,'osDpGetCounters  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E04,1,'__osSpGetStatus #1'),
  ((0x3C0E3C0E,0x03E003E0,0xADC4ADC4,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C754E04,1,'__osSpSetStatus #1'),
  ((0x3C0E3C0E,0x8DC58DC5,0x27BD27BD,0x30AF30AF,0x15E015E0,0x00000000,0x10001000,0x24022402),0x000010DC,0x785CE920,1,'__osSpSetPc #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0x62EFF3C3,1,'__osSpRawReadIo  #1'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C33449C,1,'__osSpDeviceBusy #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0xC75BF3C3,1,'__osSpRawWriteIo  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFA7AFA7,0x10401040),0x00000681,0x7F2A4C47,1,'__osSpRawStartDma #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0x8FA48FA4,0xAFA2AFA2,0x8FAE8FAE,0x8DCF8DCF),0x00001301,0xF94620D3,39,'osSpTaskLoad #39'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x10401040,0x00000000,0x00000000,0x00000000),0x00002911,0x14EFB143,22,'osSpTaskStartGo #22'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0x24042404,0x8FBF8FBF,0x27BD27BD,0x03E003E0,0x00000000),0x00000029,0x0000BE43,46,'osSpTaskYield #46'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0xAFA2AFA2,0x8FAE8FAE,0x31CF31CF,0x11E011E0),0x0000C6C1,0x105EE503,47,'osSpTaskYielded #47'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x24052405,0x3C0E3C0E,0x25CE25CE),0x00003AA9,0x0A2F9EC3,1,'__osViInit  #1'),
  ((0x3C0E3C0E,0x8DC28DC2,0x304F304F,0x03E003E0,0x01E001E0,0x00000000,0x00000000,0x00000000),0x00000004,0x3C03CEF0,2,'osViGetCurrentField #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040,0x02000200),0x00008021,0xD92C2A4B,20,'osViGetCurrentFramebuffer #20'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040,0x02000200),0x00008021,0xD92C2A4B,20,'osViGetNextFramebuffer #20'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E40,2,'osViGetCurrentLine #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0x00400040),0x00000041,0xC6A8D0DB,2,'osViGetCurrentMode  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C434E40,2,'osViGetStatus #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0xAFA4AFA4,0x00000000,0x00000000),0x0000AC16,0xF87FBB1C,55,'osCreateViManager #55'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000004,0x00CCEA0F,1,'__osViGetCurrentContext  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x3C0F3C0F),0x00002101,0x506399BB,17,'osViSetEvent #17'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x3C0F3C0F,0x8DEF8DEF,0x8FAE8FAE),0x00008A41,0xACCF63FB,2,'osViSetMode #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x8FAE8FAE,0x00400040,0x31CF31CF),0x00002981,0x4C2FEFFB,2,'osViSetSpecialFeatures #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xE7ACE7AC,0xAFB1AFB1,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE),0x00009081,0xC66E162B,2,'osViSetXScale  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xE7ACE7AC,0x00000000,0xAFB0AFB0,0x3C0E3C0E,0x8DCE8DCE,0xC7A4C7A4),0x00004841,0xED0B93EB,2,'osViSetYScale  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x00000000,0xAFA4AFA4,0x3C0F3C0F,0x8DEF8DEF,0x8FAE8FAE,0xAFA2AFA2),0x00001421,0x4A93A603,23,'osViSwapBuffer #23'),
  ((0x27BD27BD,0xAFB1AFB1,0xAFBFAFBF,0xAFB2AFB2,0xAFB0AFB0,0xAFA0AFA0,0x3C113C11,0x3C0E3C0E),0x00000901,0xFB6943CF,1,'__osViSwapContext  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFB0AFB0,0x93AE93AE,0x00400040,0x11C011C0),0x00003481,0x2C1E6BFB,2,'osViBlack #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x93AE93AE,0x00400040),0x00003101,0xF96DDABB,2,'osViFade  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C5B4E80,1,'__osSiGetStatus  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0x62EFF3C3,1,'__osSiRawReadIo #1'),
  ((0x3C0E3C0E,0x8DC48DC4,0x27BD27BD,0x308F308F,0x11E011E0,0x00000000,0x10001000,0x24022402),0x000004DC,0x3C334410,1,'__osSiDeviceBusy #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x000001A1,0xC75BF3C3,1,'__osSiRawWriteIo #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x10401040,0x00000000,0x10001000),0x00008DA1,0xCFAFF3C3,1,'__osSiRawStartDma #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x3C0E3C0E,0x91CE91CE,0x11C011C0),0x000050C1,0x344E73D3,42,'osContStartQuery #42'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x8FA58FA5,0x00000000,0x27A427A4,0x8FBF8FBF,0x27BD27BD),0x000000A1,0x000E46D3,43,'osContGetQuery #43'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0x3C043C04,0x3C053C05,0xAC2EAC2E,0x24A524A5),0x000015C5,0x434E72C3,1,'__osSiCreateAccessQueue #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x00000000,0x00000000),0x00005616,0x274FB39C,1,'__osSiGetAccess #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x00000000,0x00000000,0x8FBF8FBF),0x00000109,0x000D6BC3,1,'__osSiRelAccess #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x3C0E3C0E,0x91CE91CE,0x24012401),0x0000A1C1,0x846C33D3,26,'osContStartReadData #26'),
  ((0x3C0F3C0F,0x91EF91EF,0x3C0E3C0E,0x27BD27BD,0x25CE25CE,0xAFAEAFAE,0x19E019E0,0xAFA0AFA0),0x0000025A,0x86C18908,27,'osContGetReadData #27'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA5AFA5,0x3C0E3C0E,0x91CE91CE,0x24012401),0x0000A1C1,0x846C32D3,2,'osContReset  #2'),
  ((0x27BD27BD,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01,0x000E000E,0x002F002F,0xAC20AC20),0x0000A781,0xFCECCE97,1,'__osPackResetData  #1'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x11C011C0),0x00004A85,0x04BA4E47,25,'osContInit #25'),
  ((0x3C0F3C0F,0x91EF91EF,0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xA3A0A3A0,0xAFAEAFAE,0x19E019E0),0x00000496,0x6D7C65D8,1,'__osContGetInitData  #1'),
  ((0x27BD27BD,0x30843084,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01,0x000E000E,0x002F002F),0x00004F03,0x19C74027,1,'__osPackRequestData  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFA6AFA6,0x8FA48FA4,0x00000000),0x00002801,0xCF9F02EB,2,'osPfsReFormat  #2'),
  ((0x27BD27BD,0x8FB88FB8,0x3C0E3C0E,0x25CE25CE,0x240F240F,0x24012401,0xAFBFAFBF,0xAFA4AFA4),0x00004039,0x28E40ACB,1,'__osContRamWrite  #1'),
  ((0x27BD27BD,0x30843084,0xA3A0A3A0,0xAFA0AFA0,0x93AE93AE,0x31CF31CF,0x11E011E0,0x00000000),0x0000A363,0xB1DAA457,1,'__osContAddressCrc  #1'),
  ((0x27BD27BD,0xA3A0A3A0,0xAFA0AFA0,0x240E240E,0xAFAEAFAE,0x93AF93AF,0x31F831F8,0x13001300),0x000086C9,0x915A314B,1,'__osContDataCrc  #1'),
  ((0x27BD27BD,0xAFA0AFA0,0xAFA4AFA4,0x18A018A0,0xAFA0AFA0,0x8FAF8FAF,0x8FAE8FAE,0x8FAB8FAB),0x00000609,0x27AAAE2F,1,'__osSumcalc  #1'),
  ((0x27BD27BD,0xA7A0A7A0,0xA4C0A4C0,0x94CE94CE,0xA4AEA4AE,0xAFA0AFA0,0x8FAF8FAF,0x008F008F),0x00000001,0x458111C3,1,'__osIdCheckSum  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA0AFA0,0xA3A0A3A0),0x00000201,0x84084413,1,'__osRepairPackId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA0AFA0,0x91CF91CF,0x11E011E0),0x00004081,0x38EAD507,1,'__osCheckPackId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0x91CF91CF,0x11E011E0,0x00000000,0xA1C0A1C0),0x00005021,0x0985F787,1,'__osGetId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0x91CF91CF,0x11E011E0,0x00000000,0xA1C0A1C0),0x00005021,0x09D5F787,1,'__osCheckId  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x91CF91CF),0x00008101,0x955F1907,1,'__osPfsRWInode  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA0AFA0,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x91CF91CF),0x00003801,0x5138124B,1,'__osPfsSelectBank  #1'),
  ((0x27BD27BD,0x3C0E3C0E,0xAFBFAFBF,0x25CE25CE,0x240F240F,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6),0x00004019,0x18741AD7,1,'__osContRamRead  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA0AFA0,0x00000000,0x8FA48FA4,0xAFA2AFA2,0x8FAE8FAE),0x00008301,0x4D40AA6B,2,'osPfsChecker  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0x8FAE8FAE,0x8FAF8FAF,0x01CF01CF),0x00009C01,0x014D1113,0,'corrupted_init'),
  ((0x27BD27BD,0xAFA5AFA5,0x93B893B8,0x93AE93AE,0xAFA4AFA4,0x8FAA8FAA,0xAFBFAFBF,0xAFA6AFA6),0x00009001,0xBB51277F,0,'corrupted'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFA0AFA0,0x8FA48FA4),0x0000A001,0x5665DA13,2,'osPfsInit  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0x00000000,0x00000000,0x3C053C05),0x0000A501,0x096DBBE3,1,'__osPfsGetStatus  #1'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0),0x0000A401,0x59FF4E7B,2,'osPfsAllocateFile  #2'),
  ((0x27BD27BD,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x19C019C0),0x00000681,0xC690E4B3,1,'__osPfsDeclearPage  #1'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0x11C011C0),0x00003481,0x2E454E7B,2,'osPfsDeleteFile  #2'),
  ((0x27BD27BD,0xAFA6AFA6,0x93B893B8,0xAFA5AFA5,0x8FAF8FAF,0x00180018,0xAFBFAFBF,0xAFA4AFA4),0x00009001,0x82C6EE97,1,'__osPfsReleasePages  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA7AFA7,0x93AE93AE,0x8FAF8FAF,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6),0x00004001,0x38E7B6E7,1,'__osBlockSum  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAF8FAF,0xAFA5AFA5,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0x8FAE8FAE),0x0000C401,0x4A78E67F,2,'osPfsReadWriteFile  #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAF8FAF,0xAFA5AFA5,0xAFBFAFBF,0xAFA6AFA6,0x8FAE8FAE,0x8DF88DF8),0x00006201,0x4F0300D7,2,'osPfsFileState  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0,0x00000000),0x00003601,0x1E461E43,2,'osPfsFindFile  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0x8FA48FA4,0x24012401,0x14411441),0x000016C1,0xE8DA9EBB,2,'osPfsSetLabel  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x8FAE8FAE,0xAFBFAFBF,0xAFA4AFA4,0x15C015C0,0xAFA6AFA6,0x10001000),0x0000D9A1,0x4BDFCAAB,2,'osPfsGetLabel  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0xA3A0A3A0,0x00000000),0x00005005,0xB44C11C3,2,'osPfsIsPlug  #2'),
  ((0x27BD27BD,0x30843084,0x3C013C01,0xA024A024,0xAFA0AFA0,0x8FAE8FAE,0x8FB88FB8,0x3C013C01),0x00003C0B,0x33D1AD07,1,'__osPfsRequestData  #1'),
  ((0x3C0F3C0F,0x91EF91EF,0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xA3A0A3A0,0xAFAEAFAE,0x19E019E0),0x00000496,0x6D7C65D8,1,'__osPfsGetInitData  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA0AFA0,0xAFA0AFA0,0x8DCF8DCF),0x00009B01,0x860246BB,2,'osPfsFreeBlocks  #2'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA0AFA0,0x8DCF8DCF),0x00009B01,0x96025FAF,2,'osPfsNumFiles  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x97AE97AE,0xAFBFAFBF,0xAFA4AFA4,0xAFA6AFA6,0xAFA7AFA7,0xAFA0AFA0),0x00004001,0xE5354E7B,2,'osPfsReSizeFile  #2'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AF93AF,0x3C0E3C0E,0x25CE25CE,0x29E129E1,0xAFBFAFBF,0xAFA4AFA4),0x00006831,0xCFF4A5D7,58,'osEepromRead #58'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AF93AF,0x3C0E3C0E,0x25CE25CE,0x29E129E1,0xAFBFAFBF,0xAFA4AFA4),0x00003431,0x0E64A5D7,59,'osEepromWrite #59'),
  ((0x27BD27BD,0x3C0E3C0E,0x25CE25CE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA0AFA0,0xAFAEAFAE),0x0000C005,0x0A462BA7,1,'__osEepStatus #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0x00000000,0xAFA0AFA0,0x8FA48FA4,0x00000000,0x27A527A5),0x00006481,0x396AB7D3,57,'osEepromProbe #57'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0x29C129C1,0xAFA6AFA6,0xAFA7AFA7),0x00002D21,0x971CBD47,61,'osEepromLongWrite #61'),
  ((0x27BD27BD,0xAFA5AFA5,0x93AE93AE,0xAFBFAFBF,0xAFA4AFA4,0x29C129C1,0xAFA6AFA6,0xAFA7AFA7),0x00002D21,0x971CBD47,60,'osEepromLongRead #60'),
  ((0x3C023C02,0x03E003E0,0x8C428C42,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x00CBEA0F,2,'osPiGetDeviceType  #2'),
  ((0x3C0E3C0E,0x03E003E0,0x8DC28DC2,0x00000000,0x00000000,0x00000000,0x00000000,0x00000000),0x00000000,0x3C534E60,2,'osPiGetStatus  #2'),
  ((0x3C0E3C0E,0x8DC68DC6,0x27BD27BD,0x30CF30CF,0x11E011E0,0x00000000,0x3C183C18,0x8F068F06),0x0000031C,0x106FF910,2,'osPiRawReadIo  #2'),
  ((0x3C0E3C0E,0x8DC68DC6,0x27BD27BD,0x30CF30CF,0x11E011E0,0x00000000,0x3C183C18,0x8F068F06),0x0000431C,0x106FF910,2,'osPiRawWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFB1AFB1,0xAFB0AFB0),0x00008C01,0x83360A7B,2,'osPiRawStartDma #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x15C015C0),0x00008085,0xFA781B07,2,'osCreatePiManager #2'),
  ((0x3C0E3C0E,0x8DC78DC7,0x27BD27BD,0x30EF30EF,0x11E011E0,0x00000000,0x3C183C18,0x8F078F07),0x0000031C,0x6CEDB894,2,'osEPiRawReadIo #2'),
  ((0x3C0E3C0E,0x8DC78DC7,0x27BD27BD,0x30EF30EF,0x11E011E0,0x00000000,0x3C183C18,0x8F078F07),0x0000231C,0x6CEDB894,2,'osEPiRawWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xAFB1AFB1,0xAFB0AFB0),0x00008C01,0x83360A7B,2,'osEPiRawStartDma  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FA48FA4),0x00000001,0x0E6D59BB,2,'osEPiWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0x00000000,0xAFB0AFB0,0x8FA48FA4),0x00000001,0x0E6D59BB,2,'osEPiReadIo  #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFB1AFB1),0x00000D05,0xD9187407,37,'osEPiStartDma #37'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x15C015C0,0x00000000,0x03E003E0,0x00000000,0x00000000,0x00000000),0x00000006,0x00313A6F,2,'osPiGetCmdQueue  #2'),
  ((0x3C013C01,0x27BD27BD,0xA020A020,0xAFBFAFBF,0x3C013C01,0x3C0E3C0E,0xAFA0AFA0,0xAC2EAC2E),0x0000C186,0x584E9288,2,'osCartRomInit  #2'),
  ((0x240E240E,0x3C013C01,0xA02EA02E,0x3C013C01,0x3C0F3C0F,0xAC2FAC2F,0x3C013C01,0x24182418),0x0000EDA5,0x385030D6,2,'osLeoDiskInit  #2'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x10001000,0x00000000),0x00000A56,0x6357077C,1,'__osLeoInterrupt  #1'),
  ((0x27BD27BD,0xAFA4AFA4,0x8FAE8FAE,0xAFBFAFBF,0xAFA0AFA0,0xAFA0AFA0,0xAFA0AFA0,0xAFAEAFAE),0x00008601,0x1D4D8107,1,'__osDevMgrMain #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x240E240E,0x3C013C01,0x3C043C04,0x3C053C05,0xAC2EAC2E,0x24A524A5),0x000015C5,0x434E72C3,1,'__osPiCreateAccessQueue  #1'),
  ((0x3C0E3C0E,0x8DCE8DCE,0x27BD27BD,0xAFBFAFBF,0x15C015C0,0x00000000,0x00000000,0x00000000),0x00005616,0x274FB39C,1,'__osPiGetAccess  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0x3C043C04,0x24842484,0x00000000,0x00000000,0x00000000,0x8FBF8FBF),0x00000109,0x000D6BC3,1,'__osPiRelAccess  #1'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FA48FA4,0x00000000),0x00008001,0xDA1D0ABB,2,'osPiWriteIo  #2'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0x00000000,0xAFB0AFB0,0x8FA48FA4,0x00000000),0x00008001,0xDA1D0ABB,2,'osPiReadIo  #2'),
  ((0x27BD27BD,0x3C0E3C0E,0x8DCE8DCE,0xAFBFAFBF,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7),0x00005A05,0x1E15B407,12,'osPiStartDma #12'),
  ((0x28C128C1,0x14201420,0x00850085,0x30423042,0x14401440,0x00040004,0x33183318,0x13001300),0x0000C0DB,0xBB8C0CCE,0,'bcmp'),
  ((0x10C010C0,0x00A000A0,0x10851085,0x00A400A4,0x54205420,0x28C128C1,0x00860086,0x00A200A2),0x0000BE25,0xD1D5189A,0,'bcopy'),
  ((0x28A128A1,0x14201420,0x00040004,0x30633063,0x10601060,0x00A300A3,0xA880A880,0x00830083),0x0000251B,0x5980BB1D,0,'bzero'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DDDB1,0,'A__ull_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ull_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x182E8DB1,3,'A__ull_div #3'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DFDB1,0,'A__ll_lshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x15E015E0),0x00000080,0x180E8DB1,5,'A__ll_rem #5'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E9DB1,6,'A__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00000000,0x00432DB1,4,'A__ll_mul #4'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x87AF87AF,0xAFA6AFA6,0xAFA7AFA7,0xDFAEDFAE,0x01E001E0,0x03000300,0x01D901D9,0x17201720),0x00000080,0xD4AEE0B3,0,'A__ull_divremi'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF),0x00002201,0xBC4E2F5B,0,'A__ll_mod'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01EE01EE,0x00020002),0x00000000,0x000DCDB1,0,'A__ll_rshift'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFBFAFBF,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0x3C043C04,0x24842484),0x00000181,0xCA649E3B,0,'sprintf'),
  ((0x00800080,0x10C010C0,0x00A000A0,0x906E906E,0x24C624C6,0x24422442,0x24632463,0x14C014C0),0x000000F2,0x001E42BD,0,'memcpy'),
  ((0x908E908E,0x00800080,0x11C011C0,0x00000000,0x906F906F,0x24632463,0x55E055E0,0x906F906F),0x00000024,0x0006FCD8,0,'strlen'),
  ((0x90839083,0x30AE30AE,0x30A230A2,0x51C351C3,0x00800080,0x54605460,0x90839083,0x03E003E0),0x00000006,0x00018CBE,0,'strchr'),
  ((0x27BD27BD,0xAFB7AFB7,0xAFB6AFB6,0xAFB5AFB5,0xAFBEAFBE,0xAFB4AFB4,0xAFB3AFB3,0xAFA7AFA7),0x00000001,0x486FA0F3,0,'_Printf'),
  ((0x27BD27BD,0xAFB1AFB1,0x30A230A2,0x24032403,0x00800080,0xAFBFAFBF,0xAFB3AFB3,0xAFB2AFB2),0x0000B20D,0x3A6991FF,0,'_Litob'),
  ((0x27BD27BD,0xAFA4AFA4,0xAFBFAFBF,0xAFA6AFA6,0xAFA7AFA7,0x00C000C0,0x00E000E0,0x8FA78FA7),0x00000001,0xD14D8F7F,0,'lldiv'),
  ((0x00A600A6,0x00000000,0x27BD27BD,0x14C014C0,0x00000000,0x00070007,0x24012401,0x14C114C1),0x000042CC,0x500B111E,0,'ldiv'),
  ((0x27BD27BD,0xAFBFAFBF,0xAFB5AFB5,0xAFB4AFB4,0xAFB3AFB3,0xAFB2AFB2,0xAFB1AFB1,0xAFB0AFB0),0x00009001,0xFEF33863,0,'_Ldtob'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E964B,6,'__ll_div #6'),
  ((0xAFA4AFA4,0xAFA5AFA5,0xAFA6AFA6,0xAFA7AFA7,0xDFAFDFAF,0xDFAEDFAE,0x01CF01CF,0x00000000),0x00009100,0xF28E964B,6,'A__ll_div #6'),
]
ULTRAHLE_OSPATCH: List[str] = [
  'osSpTaskLoad #39',
  'osSpTaskStartGo #22',
  'osSpTaskYield #46',
  'osSpTaskYielded #47',
  '__osSpSetStatus #1',
  '__osSpSetPc #1',
  '__osSpRawStartDma #1',
  '__osSpDeviceBusy #1',
  '__osSpGetStatus #1',
  '__ull_rshift #9',
  '__ull_rem #5',
  '__ull_div #3',
  '__ll_lshift #9',
  '__ll_rem #5',
  '__ll_div #6',
  '__ll_mul #4',
  '__ull_divremi #9',
  '__ll_mod #9',
  '__ll_rshift #9',
  'osSetTime #2',
  'osMapTLB #24',
  'osMapTLBRdb #2',
  'osCreateMesgQueue #13',
  'osSetEventMesg #16',
  'osViSetEvent #17',
  'osCreateThread #10',
  'osRecvMesg #14',
  'osViGetCurrentField #2',
  'osViGetCurrentLine #2',
  'osViGetStatus #2',
  'osSendMesg #15',
  'osStartThread #11',
  'osStopThread #28',
  'osWriteBackDCacheAll #1',
  'osCreateViManager #55',
  'osViSetMode #2',
  'osViBlack #2',
  'osViSetSpecialFeatures #2',
  'osCreatePiManager #2',
  'osSetThreadPri #18',
  'osInitialize #2',
  'osViSwapBuffer #23',
  'osViGetCurrentFramebuffer #20',
  'osViGetNextFramebuffer #20',
  'osContStartReadData #26',
  'osContGetReadData #27',
  'osContStartQuery #42',
  'osContGetQuery #43',
  'osContInit #25',
  'osEepromProbe #57',
  'osInvalDCache #1',
  'osInvalICache #38',
  'osPiStartDma #12',
  'osEPiStartDma #37',
  'osInvalCache #1',
  'osEepromLongRead #60',
  'osEepromLongWrite #61',
  'osGetTime #19',
  'osAiSetFrequency #32',
  'osWriteBackDCache #2',
  'osAiGetLength #31',
  'osAiSetNextBuffer #30',
  'osVirtualToPhysical #21',
  'osPhysicalToVirtual #29',
  'osGetThreadPri #2',
  'osGetCount #48',
  'osPiRawStartDma #2',
  'osMapTLBRdb #2',
  'osEPiRawReadIo #2',
  'osSetTimer #33',
  'osStopTimer #34',
  'osEepromWrite #59',
  'osJamMesg #15',
  'osEepromRead #58',
  'osSetIntMask #2',
  '__osDisableInt #1',
  '__osRestoreInt #1',
  '__ososViDevMgrMain #1',
  '__ososContGetInitData #1',
  '__ososPackRequestData #1',
  '__ososTimerServicesInit #1',
  '__ososTimerInterrupt #1',
  '__ososSetTimerIntr #1',
  '__ososInsertTimer #1',
  '__ososViInit #1',
  '__ososExceptionPreamble #1',
  '__ososEnqueueAndYield #1',
  '__ososEnqueueThread #1',
  '__ososPopThread #1',
  '__ososDispatchThread #1',
  '__ososCleanupThread #1',
  '__ososPiCreateAccessQueue #1',
  '__ososPiGetAccess #1',
  '__ososPiRelAccess #1',
  '__osDevMgrMain #1',
  '__osGetSR #1',
  '__osSetFpcCsr #1',
  '__osSiRawReadIo #1',
  '__osSiRawWriteIo #1',
  '__osSiCreateAccessQueue #1',
  '__osSiGetAccess #1',
  '__osSiRelAccess #1',
  '__osSiRawStartDma #1',
  '__osEepStatus #1',
  '__osAiDeviceBusy #1',
  '__osSetCompare #1',
  '__osProbeTLB #1',
  '__osSyncPutChars #1',
  '__osSiDeviceBusy #1',
  '__ososAtomicDec #1',
  '__osViDevMgr #1',
  '__osPiDevMgr #1',
  '__osRunQueue #1',
  '__osActiveQueue #1',
  '__osRunningThread #1',
  '__osViNext #1',
  '__osPiAccessQueueEnabled #1',
  '__osRcpImTable #1',
  '__osEventStateTab #1',
  '__osMyViThread #1',
  '__osMyViStack #1',
  '__osMyViQueue #1',
  '__osMyViMesg #1',
  '__osCurrentTime #1',
  '__osCurrentTime_2 #1',
  '__osBaseCounter #1',
  '__os* #1',
  'os* #2',
]
ULTRAHLE_DISABLE_PATCHES: Tuple[str, ...] = (
  'osPiGetDeviceType',
  'osPiGetStatus',
  'osPiRawReadIo',
  'osPiRawWriteIo',
  'osPiRawStartDma',
  'osPiGetCmdQueue',
  '__osPiDevMgr',
  '__osPiTable',
  '__osPiAccessQueueEnabled',
  '__osPiCreateAccessQueue',
  '__osPiGetAccess',
  '__osPiRelAccess',
  'osPiWriteIo',
  'osPiReadIo',
  '__osPfsPifRam',
  'osPfsReFormat',
  '__osPfsRWInode',
  '__osPfsSelectBank',
  'osPfsInit',
  '__osPfsGetStatus',
  'osPfsAllocateFile',
  '__osPfsDeclearPage',
  'osPfsDeleteFile',
  '__osPfsReleasePages',
  'osPfsReadWriteFile',
  'osPfsFileState',
  'osPfsFindFile',
  'osPfsSetLabel',
  'osPfsGetLabel',
  'osPfsIsPlug',
  '__osPfsRequestData',
  '__osPfsGetInitData',
  'osPfsFreeBlocks',
  'osPfsNumFiles',
  'osPfsReSizeFile',
  # Cont/SI: keep HLE patches enabled — __osException is patched to skip, so
  # hardware SI completion never runs; ContStartReadData must fire OS_EVENT_SI.
  'osContReset',
  '__osContRamWrite',
  '__osContAddressCrc',
  '__osContDataCrc',
  '__osContRamRead',
  '__osContPifRam',
  '__osContLastCmd',
  '__osContinitialized',
  '__osSiGetStatus',
  '__osSiRawReadIo',
  '__osSiDeviceBusy',
  '__osSiRawWriteIo',
  '__osSiRawStartDma',
  '__osSiCreateAccessQueue',
  '__osSiGetAccess',
  '__osSiRelAccess',
  '__osSiAccessQueue',
  '__osSiAccessQueueEnabled',
  '__osGetCause',
  '__osGetCompare',
  '__osGetConfig',
  '__osGetFpcCsr',
  '__osGetSR',
  '__osGetTLBASID',
  '__osGetTLBHi',
  '__osGetTLBLo0',
  '__osGetTLBLo1',
  '__osGetTLBPageMask',
  '__osSetCause',
  '__osSetCompare',
  '__osSetConfig',
  '__osSetCount',
  '__osSetFpcCsr',
  '__osSetSR',
)
ULTRAHLE_INI_PROFILES: Dict[str, Dict[str, Any]] = {
  'SUPER MARIO': {
      'alttitle': 'Super Mario 64', 'osrange': (0x80300000, 0x80380000),
      'ismario': 1, 'optimize': 3,
  },
  'THE LEGEND ': {
      'alttitle': 'Zelda: Ocarina of Time', 'osrange': (0x80001000, 0x80008000),
      'iszelda': 1, 'optimize': 3,
      'patches': [
          (0, 0x80005BA0, 'patch', 2),
          (0, 0x80003500, 'patch', 2),
          (0, 0x800012A0, 'patch', 2),
          (0, 0x80001600, 'patch', 2),
          (0, 0x80005130, 'patch', 2),
          (-1, 0x8011B9D9, 'byte', 1),  # English
      ],
  },
  'ZELDA': {'alttitle': 'Zelda', 'osrange': (0x80001000, 0x80010000), 'iszelda': 1, 'optimize': 3},
  'Wave Race': {'osrange': (0x800C0000, 0x800F0000)},
  'WAVE RACE': {'osrange': (0x800C0000, 0x800F0000)},
  'Banjo-Kazooie': {
      'bootloader': 1, 'osrange': (0x80000000, 0x80010000),
      'patches': [
          (0, 0x8000052C, 'patch', 49),
          (0, 0x80000530, 'word', 0x0320F809),
          (0, 0x80000534, 'word', 0x8FA40020),
      ],
  },
  'BANJO': {
      'bootloader': 1, 'osrange': (0x80000000, 0x80010000),
      'patches': [
          (0, 0x8000052C, 'patch', 49),
          (0, 0x80000530, 'word', 0x0320F809),
          (0, 0x80000534, 'word', 0x8FA40020),
      ],
  },
  'GoldenEye': {'osrange': (0x80008000, 0x80024000)},
  'GOLDENEYE': {'osrange': (0x80008000, 0x80024000)},
  'MARIOKART': {'osrange': (0x80000000, 0x80100000)},
  'MARIO KART': {'osrange': (0x80000000, 0x80100000)},
  'STAR FOX': {'osrange': (0x80000000, 0x80100000)},
  'STARFOX': {'osrange': (0x80000000, 0x80100000)},
  'F-ZERO': {'bootloader': 1, 'osrange': (0x80000000, 0x80100000)},
  'DONKEY KONG': {'osrange': (0x80000000, 0x80100000)},
  'PAPER MARIO': {'osrange': (0x80000000, 0x80100000)},
  'SMASH BROS': {'osrange': (0x80000000, 0x80100000)},
  'Doom': {'osrange': (0x80000000, 0x80100000)},
  'DOOM': {'osrange': (0x80000000, 0x80100000)},
  'Quake': {'osrange': (0x80000000, 0x80100000)},
  'QUAKE': {'osrange': (0x80000000, 0x80100000)},
}


# ── UltraHLE SYM.C / PATCH install (signature scan + OP_PATCH rewrite) ──
ADDRMASK_UH = 0x3FFFFFFF
ULTRAHLE_CODESIZE = 0x100000  # boot.c cart.codesize default


def _uh_op_op(word: int) -> int:
    return (word >> 26) & 0x3F


def _uh_op_imm(word: int) -> int:
    return word & 0xFFFF


def ultrahle_match_ini(title: str) -> Dict[str, Any]:
    t = (title or "").upper()
    for key, prof in ULTRAHLE_INI_PROFILES.items():
        if t.startswith(key.upper()) or key.upper() in t:
            return dict(prof)
    # title field is often "SUPER MARIO 64      "
    for key, prof in ULTRAHLE_INI_PROFILES.items():
        if key.upper().rstrip() in t:
            return dict(prof)
    return {}


class UltraHleSym:
    """Port of UltraHLE sym.c — find libultra by CRC and rewrite to OP_PATCH."""

    __slots__ = (
        "core", "syms", "found", "patches_applied", "first_patch", "last_patch",
        "osrange", "ismario", "iszelda", "bootloader", "ini_patches",
        "codebase", "codesize", "last_report", "yield_addrs",
    )

    def __init__(self, core: "ACsN64Core"):
        self.core = core
        self.reset()

    def reset(self):
        self.syms: List[Dict[str, Any]] = [{"addr": 0, "text": "(null)", "patch": 0, "original": 0}]
        self.found: Dict[int, Dict[str, Any]] = {}
        self.patches_applied = 0
        self.first_patch = 0
        self.last_patch = 0
        self.osrange = (0, 0)
        self.ismario = 0
        self.iszelda = 0
        self.bootloader = 0
        self.ini_patches: List[Tuple] = []
        self.codebase = 0x80000400
        self.codesize = ULTRAHLE_CODESIZE
        self.last_report = ""
        self.yield_addrs: set = set()

    def _rd32(self, addr: int) -> int:
        return self.core.bus.read_u32(u32(addr))

    def _wr32(self, addr: int, val: int):
        self.core.bus.write_u32(u32(addr), u32(val))

    def _disabled(self, name: str) -> bool:
        base = name.split("#", 1)[0].strip()
        for d in ULTRAHLE_DISABLE_PATCHES:
            if base == d or base.startswith(d):
                return True
        return False

    def add_symbol(self, addr: int, text: str, patch: int) -> int:
        addr &= ADDRMASK_UH
        if self._disabled(text):
            patch = 0
        # replace existing
        for i, s in enumerate(self.syms):
            if s["addr"] == addr:
                s["text"] = text
                s["patch"] = patch
                return i
        self.syms.append({"addr": addr, "text": text, "patch": patch, "original": 0})
        return len(self.syms) - 1

    def find_symbol_name(self, addr: int) -> str:
        addr &= ADDRMASK_UH
        best = None
        best_a = -1
        for s in self.syms:
            if s["addr"] == addr:
                return s["text"]
            if best_a < s["addr"] <= addr:
                best_a = s["addr"]
                best = s
        if best is None:
            return "?"
        off = addr - best["addr"]
        if off > 99999:
            return "?"
        if off == 0:
            return best["text"]
        return f"?{off}+{best['text']}"

    def routine_crc2(self, addr: int, crc1_in: int) -> Tuple[int, int]:
        """UltraHLE routinecrc2(addr, barrier=0) — CRC test against known crc1."""
        crc1 = crc1_in
        crc2 = 0
        x1 = self._rd32(addr)
        if not (x1 & 0xFFFFFF):
            return (-1, -1)
        inn = 16
        for i in range(16):
            x1 = self._rd32(addr + i * 4)
            if x1 == 0x03E00008:  # JR RA
                inn = min(i + 2, 16)
                break
        for i in range(inn):
            x1 = self._rd32(addr + i * 4)
            crc = i
            op = _uh_op_op(x1)
            if op in (2, 3):  # J / JAL
                crc += op
            elif op == 15:  # LUI
                imm = _uh_op_imm(x1)
                if 0xA400 <= imm <= 0xAFFF:
                    crc2 = u32(crc2 + x1)
                else:
                    crc += op
            elif op == 16 or op == 17:  # COP0 / COP1
                crc2 ^= x1
                crc = 0
            else:
                if crc1 & (1 << i):
                    crc ^= (x1 >> 16)
                else:
                    crc ^= x1
            x1 = crc
            if inn < 4:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 = (x1 & 255) << (i * 8)
            elif inn < 8:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 ^= (x1 >> 4)
                x1 = (x1 & 15) << (i * 4)
            else:
                x1 ^= (x1 >> 16)
                x1 ^= (x1 >> 8)
                x1 ^= (x1 >> 4)
                x1 ^= (x1 >> 2)
                x1 = (x1 & 3) << (i * 2)
            crc2 ^= x1
        return (crc1, u32(crc2))

    def patch_names(self):
        """Assign patch ids from ospatch[] patterns (sym_patchnames)."""
        patterns = []
        for entry in ULTRAHLE_OSPATCH:
            sp = entry.find(" ")
            if sp < 0:
                continue
            namepart = entry[:sp]
            wild = namepart.endswith("*")
            nlen = len(namepart) - (1 if wild else 0)
            hashp = entry.find("#")
            pnum = int(entry[hashp + 1:]) if hashp >= 0 else 0
            patterns.append((namepart[:nlen], wild, nlen, pnum, entry))
        for i, s in enumerate(list(self.syms)):
            text = s["text"]
            if "%" in text:
                continue
            if "#" in text and s["patch"]:
                continue
            if s["patch"]:
                continue
            base = text.split("#", 1)[0].strip()
            for npart, wild, nlen, pnum, _full in patterns:
                if len(base) < nlen:
                    continue
                if base[:nlen].lower() != npart.lower():
                    continue
                if not wild and len(base) > nlen and base[nlen] > " ":
                    continue
                self.add_symbol(s["addr"], f"{base} #{pnum}", pnum)
                break

    def find_os_calls(self, base: int, nbytes: int, cont: int = 0) -> str:
        """sym_findoscalls — scan memory for oscall[] signatures."""
        if nbytes <= 0:
            self.last_report = "empty range"
            return self.last_report
        base = u32(base | 0x80000000)
        end = u32(base + nbytes)
        # Working copy of oscall state
        state = []
        for data, crc1, crc2, patch, name in ULTRAHLE_OSCALL:
            state.append({
                "data": data, "crc1": crc1, "crc2": crc2, "patch": patch, "name": name,
                "flag": 0, "symb": 0, "found_at": 0, "fclass": 0,
            })
        total = len(state)
        for i in range(end - 4, base - 1, -4):
            x0 = self._rd32(i)
            if not (x0 & 0xFFFFFF):
                continue
            hits = []
            for j, e in enumerate(state):
                if e["found_at"]:
                    continue
                d0 = e["data"][0]
                if d0 and ((x0 ^ d0) >> 16):
                    continue
                ok = True
                for k in range(1, 8):
                    x = self._rd32(i + k * 4)
                    y = e["data"][k]
                    if y and ((x ^ y) >> 16):
                        ok = False
                        break
                if not ok:
                    continue
                if not e["symb"]:
                    e["symb"] = i
                e["flag"] = 1
                hits.append(j)
            if not hits:
                continue
            if self.find_symbol_name(i) != "?":
                for j in hits:
                    state[j]["flag"] = 0
                continue
            found = 0
            class_ = 0
            cnt16 = 0
            for j in hits:
                e = state[j]
                _c1, y = self.routine_crc2(i, e["crc1"])
                cl = 0
                if e["crc2"] == y:
                    cl = 16
                else:
                    yy = y ^ e["crc2"]
                    for k in range(0, 32, 2):
                        if not (yy & (3 << k)):
                            cl += 1
                if cl > class_:
                    class_ = cl
                    if class_ == 16:
                        cnt16 += 1
                    found = j
                    e["flag"] = 2
                else:
                    e["flag"] = 1
            if class_ > 8:
                j = found
                if cnt16 > 1:
                    for jj in hits:
                        if state[jj]["flag"] == 2 and not state[jj]["fclass"]:
                            j = jj
                            break
                e = state[j]
                e["fclass"] = class_
                e["found_at"] = i
                e["symb"] = self.add_symbol(i, e["name"], e["patch"])
                self.found[i] = {"name": e["name"], "patch": e["patch"], "class": class_}
                nm = e["name"]
                if "EnqueueAndYield" in nm or "YieldThread" in nm:
                    self.yield_addrs.add(u32(i | 0x80000000))

            for j in hits:
                state[j]["flag"] = 0
        self.patch_names()
        cnt = sum(1 for e in state if e["found_at"])
        important = sum(1 for e in state if e["patch"] >= 10)
        imp_found = sum(1 for e in state if e["found_at"] and e["patch"] >= 10)
        self.last_report = f"OS-routine search: {cnt}/{total} found, {imp_found}/{important} important"
        return self.last_report

    def add_patches(self) -> int:
        """sym_addpatches — write PATCH(id) over every patched symbol."""
        n = 0
        first = 0xFFFFFFFF
        last = 0
        for s in self.syms:
            patch = s["patch"]
            if not patch:
                continue
            addr = s["addr"] | 0x80000000
            old = self._rd32(addr)
            if _uh_op_op(old) != ULTRAHLE_OP_PATCH:
                s["original"] = old
            self._wr32(addr, make_ultrahle_patch(patch))
            n += 1
            a = addr & ADDRMASK_UH
            if a < first:
                first = a
            if a > last:
                last = a
        self.patches_applied = n
        self.first_patch = 0 if first == 0xFFFFFFFF else first
        self.last_patch = last
        return n

    def find_first_os(self) -> str:
        if self.osrange[0] and self.osrange[1] and self.osrange[1] > self.osrange[0]:
            report = self.find_os_calls(self.osrange[0], self.osrange[1] - self.osrange[0], 0)
        else:
            # Unknown commercial title: scan a wide KSEG0 window for libultra.
            report = self.find_os_calls(0x80000000, 0x200000, 0)
        # If the profile range missed the OS, fall back to a broad rescan.
        if len(self.found) < 8 and self.osrange[0]:
            extra = self.find_os_calls(0x80000000, 0x200000, 0)
            report = f"{report}; fallback={extra}"
        return report

    def apply_game_profile(self, title: str):
        prof = ultrahle_match_ini(title)
        self.ismario = int(prof.get("ismario", 0))
        self.iszelda = int(prof.get("iszelda", 0))
        self.bootloader = int(prof.get("bootloader", 0))
        self.ini_patches = list(prof.get("patches", []))
        if "osrange" in prof:
            self.osrange = tuple(prof["osrange"])  # type: ignore
        t = (title or "").upper()
        if t.startswith("SUPER MARIO"):
            self.ismario = 1
            if not self.osrange[0]:
                self.osrange = (0x80300000, 0x80380000)
        if t.startswith("THE LEGEND") or "ZELDA" in t:
            self.iszelda = 1
        if "BANJO" in t or t.startswith("F-ZERO"):
            self.bootloader = 1

    def apply_ini_patches(self, dma_num: int = 0) -> int:
        """Port of UltraHLE inifile_patches(dmanum) for boot-time / every-frame patches."""
        n = 0
        bus = self.core.bus
        for when, addr, kind, data in self.ini_patches:
            if when != dma_num and when != -1:
                continue
            addr = u32(addr)
            kind = str(kind).lower()
            if kind == "patch":
                bus.write_u32(addr, make_ultrahle_patch(int(data)))
                n += 1
            elif kind == "word":
                bus.write_u32(addr, u32(data))
                n += 1
            elif kind == "byte":
                bus.write_u8(addr, u32(data) & 0xFF)
                n += 1
        return n

    def boot_scan_and_patch(self, title: str, codebase: int) -> str:
        self.reset()
        self.codebase = u32(codebase)
        self.apply_game_profile(title)
        report = self.find_first_os()
        n = self.add_patches()
        ini_n = self.apply_ini_patches(0)
        report = (
            f"{report}; patches={n} ini={ini_n} "
            f"flags=m{self.ismario}z{self.iszelda}b{self.bootloader} "
            f"range={self.first_patch:08X}..{self.last_patch:08X}"
        )
        self.last_report = report
        return report



def _h_PATCH(cpu, o, old_pc, g):
    """UltraHLE OP_PATCH — HLE a libultra OS routine, then return to RA."""
    patch = o.imm & 0xFFFF
    # Banjo special-case: continue at pc+4 instead of returning (PATCH.C p_banjojalr).
    if patch == 49:
        fn = ULTRAHLE_PATCH_TABLE.get(49)
        if fn: fn(cpu.core.ultrahle, cpu, g)
        return
    if patch <= 2:
        # __osEnqueueAndYield / DispatchThread were mapped to skip(#1) in UltraHLE,
        # but a pure return spins; perform a real yield into another ready thread.
        if patch == 1 and old_pc in getattr(cpu.core.uh_sym, "yield_addrs", ()):
            hle = cpu.core.ultrahle
            cur = hle.threads.get(hle.current_thread)
            if cur is not None:
                ra = u32(g[_UH_RA])
                cur["pc"] = ra
                cur["next_pc"] = u32(ra + 4)
                cur["gpr"] = list(cpu.gpr)
                cur["hi"] = cpu.hi
                cur["lo"] = cpu.lo
            if hle.schedule(0):
                return
        ra = u32(g[_UH_RA])
        cpu.pc = ra
        cpu.next_pc = u32(ra + 4)
        return
    # Stash PATCH address so blocking handlers can rewind before schedule/_save.
    cpu._patch_pc = u32(old_pc)
    fn = ULTRAHLE_PATCH_TABLE.get(patch)
    blocked = None
    if fn is not None:
        blocked = fn(cpu.core.ultrahle, cpu, g)
    if blocked == "switched":
        # Thread switch already loaded PC/GPRs — do not return to RA.
        return
    if blocked == "block":
        # Stay on the PATCH opcode (UltraHLE blocktask rewinds PC).
        cpu.pc = u32(old_pc)
        cpu.next_pc = u32(old_pc + 4)
        hle = cpu.core.ultrahle
        cur = hle.threads.get(hle.current_thread)
        if cur is not None:
            cur["pc"] = u32(old_pc)
            cur["next_pc"] = u32(old_pc + 4)
            cur["gpr"] = list(cpu.gpr)
            cur["hi"] = cpu.hi
            cur["lo"] = cpu.lo
        return
    # Default UltraHLE PATCHRET: return to caller immediately.
    ra = u32(g[_UH_RA])
    cpu.pc = ra
    cpu.next_pc = u32(ra + 4)
    # Deferred preempt: switch to a higher-pri thread woken during this PATCH.
    cpu.core.ultrahle.maybe_preempt()

def _h_GROUP(cpu, o, old_pc, g):
    """UltraHLE OP_GROUP — dynarec group marker; no-op in the interpreter."""
    pass

def _h_CACHE(cpu, o, old_pc, g): pass
def _h_SYNC(cpu, o, old_pc, g): pass
def _h_WAIT(cpu, o, old_pc, g): pass
def _h_RI(cpu, o, old_pc, g):
    cpu._raise_exception(10, old_pc)  # Reserved Instruction
def _h_CPU_UNUSABLE(cpu, o, old_pc, g):
    cpu._raise_exception(11, old_pc, ce=o.op & 3)  # Coprocessor Unusable (COP2/COP3)


# PRIMARY
for _op,_fn in [
    (0x02,_h_J),(0x03,_h_JAL),(0x04,_h_BEQ),(0x05,_h_BNE),(0x06,_h_BLEZ),(0x07,_h_BGTZ),
    (0x08,_h_ADDI),(0x09,_h_ADDIU),(0x0A,_h_SLTI),(0x0B,_h_SLTIU),(0x0C,_h_ANDI),(0x0D,_h_ORI),(0x0E,_h_XORI),(0x0F,_h_LUI),
    (0x14,_h_BEQL),(0x15,_h_BNEL),(0x16,_h_BLEZL),(0x17,_h_BGTZL),
    (0x18,_h_DADDI),(0x19,_h_DADDIU),(0x1A,_h_LDL),(0x1B,_h_LDR),
    (0x1C,_h_PATCH),(0x1D,_h_GROUP),
    (0x20,_h_LB),(0x21,_h_LH),(0x22,_h_LWL),(0x23,_h_LW),(0x24,_h_LBU),(0x25,_h_LHU),(0x26,_h_LWR),(0x27,_h_LWU),
    (0x28,_h_SB),(0x29,_h_SH),(0x2A,_h_SWL),(0x2B,_h_SW),(0x2C,_h_SDL),(0x2D,_h_SDR),(0x2E,_h_SWR),(0x2F,_h_CACHE),
    (0x30,_h_LL),(0x31,_h_LWC1),(0x32,_h_NOP),(0x33,_h_NOP),(0x34,_h_LLD),(0x35,_h_LDC1),(0x36,_h_NOP),(0x37,_h_LD),
    (0x38,_h_SC),(0x39,_h_SWC1),(0x3A,_h_NOP),(0x3B,_h_NOP),(0x3C,_h_SCD),(0x3D,_h_SDC1),(0x3E,_h_NOP),(0x3F,_h_SD),
]: _DISPATCH[_ID_PRIMARY|_op] = _fn
# SPECIAL
for _f,_fn in [
    (0x00,_h_SLL),(0x02,_h_SRL),(0x03,_h_SRA),(0x04,_h_SLLV),(0x06,_h_SRLV),(0x07,_h_SRAV),
    (0x08,_h_JR),(0x09,_h_JALR),(0x0A,_h_MOVZ),(0x0B,_h_MOVN),(0x0C,_h_SYSCALL),(0x0D,_h_BREAK),(0x0F,_h_SYNC),
    (0x10,_h_MFHI),(0x11,_h_MTHI),(0x12,_h_MFLO),(0x13,_h_MTLO),
    (0x14,_h_DSLLV),(0x16,_h_DSRLV),(0x17,_h_DSRAV),
    (0x18,_h_MULT),(0x19,_h_MULTU),(0x1A,_h_DIV),(0x1B,_h_DIVU),(0x1C,_h_DMULT),(0x1D,_h_DMULTU),(0x1E,_h_DDIV),(0x1F,_h_DDIVU),
    (0x20,_h_ADD),(0x21,_h_ADDU),(0x22,_h_SUB),(0x23,_h_SUBU),(0x24,_h_AND),(0x25,_h_OR),(0x26,_h_XOR),(0x27,_h_NOR),
    (0x2A,_h_SLT),(0x2B,_h_SLTU),(0x2C,_h_DADD),(0x2D,_h_DADDU),(0x2E,_h_DSUB),(0x2F,_h_DSUBU),
    (0x30,_h_TGE),(0x31,_h_TGEU),(0x32,_h_TLT),(0x33,_h_TLTU),(0x34,_h_TEQ),(0x36,_h_TNE),
    (0x38,_h_DSLL),(0x3A,_h_DSRL),(0x3B,_h_DSRA),(0x3C,_h_DSLL32),(0x3E,_h_DSRL32),(0x3F,_h_DSRA32),
]: _DISPATCH[_ID_SPECIAL|_f] = _fn
for _f in (0x01,0x05,0x0E,0x15,0x28,0x29,0x35,0x37,0x39,0x3D):
    _DISPATCH[_ID_SPECIAL|_f] = _h_RI
# REGIMM
for _rt,_fn in [
    (0x00,_h_BLTZ),(0x01,_h_BGEZ),(0x02,_h_BLTZL),(0x03,_h_BGEZL),
    (0x08,_h_TGEI),(0x09,_h_TGEIU),(0x0A,_h_TLTI),(0x0B,_h_TLTIU),(0x0C,_h_TEQI),(0x0E,_h_TNEI),
    (0x10,_h_BLTZAL),(0x11,_h_BGEZAL),(0x12,_h_BLTZALL),(0x13,_h_BGEZALL),
]: _DISPATCH[_ID_REGIMM|_rt] = _fn
for _rt in (0x04,0x05,0x06,0x07,0x0D,0x0F):
    _DISPATCH[_ID_REGIMM|_rt] = _h_RI
for _rt in range(0x14, 0x20):
    _DISPATCH[_ID_REGIMM|_rt] = _h_RI
# COP0_RS
for _rs,_fn in [
    (0x00,_h_MFC0),(0x01,_h_DMFC0),(0x02,_h_CFC0),(0x04,_h_MTC0),(0x05,_h_DMTC0),(0x06,_h_CTC0),(0x08,_h_BC0),
]: _DISPATCH[_ID_COP0_RS|_rs] = _fn
# COP0_CO
for _cof,_fn in [
    (0x01,_h_TLBR),(0x02,_h_TLBWI),(0x06,_h_TLBWR),(0x08,_h_TLBP),(0x18,_h_ERET),
]: _DISPATCH[_ID_COP0_CO|_cof] = _fn
_DISPATCH[_ID_COP0_CO|0x20] = _h_WAIT
for _cof in (0x00,0x03,0x04,0x05,0x07):
    _DISPATCH[_ID_COP0_CO|_cof] = _h_RI
# COP1_RS
for _rs,_fn in [
    (0x00,_h_MFC1),(0x01,_h_DMFC1),(0x02,_h_CFC1),(0x04,_h_MTC1),(0x05,_h_DMTC1),(0x06,_h_CTC1),(0x08,_h_BC1),
]: _DISPATCH[_ID_COP1_RS|_rs] = _fn
# BC1F/BC1T/BC1FL/BC1TL use _ID_COP1_BC|rt (critical for FPU branches)
for _rt in range(32):
    _DISPATCH[_ID_COP1_BC|_rt] = _h_BC1
# FPU (all format+funct combos go to _h_FPU)
for _fid in (_ID_FPU_S,_ID_FPU_D,_ID_FPU_W,_ID_FPU_L):
    for _f in range(64):
        _DISPATCH[_ID_FPU|(_fid<<6)|_f] = _h_FPU
# COP2/COP3 + reserved primary ops
for _op in (0x12, 0x13):
    _DISPATCH[_ID_PRIMARY|_op] = _h_CPU_UNUSABLE
for _op in (0x1E, 0x1F):
    _DISPATCH[_ID_PRIMARY|_op] = _h_RI
# LWC2/SWC2/LDC2/SDC2/LWC3/SWC3 are unused on VR4300 CPU — RI
for _op in (0x32, 0x33, 0x36, 0x3A, 0x3B, 0x3E):
    _DISPATCH[_ID_PRIMARY|_op] = _h_RI


# ── ACsN64Core — full emulator core ──
# ── Software RDP (state, TMEM, texel formats, combiner, blender, Z) ──
G_CYC_1CYCLE, G_CYC_2CYCLE, G_CYC_COPY, G_CYC_FILL = 0, 1, 2, 3
G_IM_FMT_RGBA, G_IM_FMT_YUV, G_IM_FMT_CI, G_IM_FMT_IA, G_IM_FMT_I = 0, 1, 2, 3, 4
G_IM_SIZ_4b, G_IM_SIZ_8b, G_IM_SIZ_16b, G_IM_SIZ_32b = 0, 1, 2, 3
# othermode_l render-mode bits
RM_AA_EN, RM_Z_CMP, RM_Z_UPD, RM_IM_RD = 0x8, 0x10, 0x20, 0x40
RM_CVG_X_ALPHA, RM_ALPHA_CVG_SEL, RM_FORCE_BL = 0x1000, 0x2000, 0x4000
ZMODE_OPA, ZMODE_INTER, ZMODE_XLU, ZMODE_DEC = 0, 1, 2, 3


def _rgba5551(px: int) -> Tuple[int, int, int, int]:
    r = (px >> 11) & 0x1F; g = (px >> 6) & 0x1F; b = (px >> 1) & 0x1F
    return (r << 3) | (r >> 2), (g << 3) | (g >> 2), (b << 3) | (b >> 2), 255 if px & 1 else 0


def _ia16(px: int) -> Tuple[int, int, int, int]:
    i = px >> 8
    return i, i, i, px & 0xFF


def z_compress(z: int) -> int:
    """18-bit RDP depth → 14-bit floating Z-buffer value (3-bit exponent, 11-bit mantissa)."""
    z &= 0x3FFFF
    if z < 0x20000: return (z >> 6) & 0x7FF
    if z < 0x30000: return (1 << 11) | ((z >> 5) & 0x7FF)
    if z < 0x38000: return (2 << 11) | ((z >> 4) & 0x7FF)
    if z < 0x3C000: return (3 << 11) | ((z >> 3) & 0x7FF)
    if z < 0x3E000: return (4 << 11) | ((z >> 2) & 0x7FF)
    if z < 0x3F000: return (5 << 11) | ((z >> 1) & 0x7FF)
    if z < 0x3F800: return (6 << 11) | (z & 0x7FF)
    return (7 << 11) | (z & 0x7FF)


_Z_DECOMP_BASE = (0x00000, 0x20000, 0x30000, 0x38000, 0x3C000, 0x3E000, 0x3F000, 0x3F800)
_Z_DECOMP_SHIFT = (6, 5, 4, 3, 2, 1, 0, 0)


def z_decompress(v: int) -> int:
    e = (v >> 11) & 7
    return _Z_DECOMP_BASE[e] + ((v & 0x7FF) << _Z_DECOMP_SHIFT[e])


# Precomputed 16-bit Z-buffer word → 18-bit depth (dz bits ignored), and 18-bit depth → stored word.
_Z_DECODE = [z_decompress(w >> 2) for w in range(0x10000)]
_Z_ENCODE = [z_compress(z) << 2 for z in range(0x40000)]


def _np_decode_tile(tm, base, line, w, h, fmt, siz, pal, tlut):
    """Vectorised TMEM → list of RGBA tuples; must match SoftRDP._decode_tile exactly."""
    np = _np
    T = np.frombuffer(bytes(tm), dtype=np.uint8)
    ys = np.arange(h).reshape(h, 1); xs = np.arange(w).reshape(1, w)
    sw = (ys & 1) * 4
    row = base + ys * line
    def pal_rgba(idx):
        e = 0x800 + (idx << 3)
        v = (T[e & 0xFFF].astype(np.uint32) << 8) | T[(e + 1) & 0xFFF]
        return conv16(v, ia=(tlut == 3))
    def conv16(v, ia=False):
        if ia:
            i = (v >> 8) & 0xFF
            return np.stack((i, i, i, v & 0xFF), axis=-1)
        r = (v >> 11) & 31; g = (v >> 6) & 31; b = (v >> 1) & 31
        return np.stack(((r << 3) | (r >> 2), (g << 3) | (g >> 2), (b << 3) | (b >> 2), np.where(v & 1, 255, 0)), axis=-1)
    if siz == G_IM_SIZ_4b:
        a = ((row + (xs >> 1)) ^ sw) & 0xFFF
        byte = T[a].astype(np.uint32)
        v = np.where(xs & 1, byte & 0xF, byte >> 4)
        if fmt == G_IM_FMT_CI or (tlut and fmt != G_IM_FMT_IA and fmt != G_IM_FMT_I):
            out = pal_rgba((pal << 4) | v)
        elif fmt == G_IM_FMT_IA:
            i = (v >> 1) * 255 // 7
            out = np.stack((i, i, i, np.where(v & 1, 255, 0)), axis=-1)
        else:
            i = v * 17
            out = np.stack((i, i, i, i), axis=-1)
    elif siz == G_IM_SIZ_8b:
        a = ((row + xs) ^ sw) & 0xFFF
        v = T[a].astype(np.uint32)
        if fmt == G_IM_FMT_CI or (tlut and fmt == G_IM_FMT_RGBA):
            out = pal_rgba(v)
        elif fmt == G_IM_FMT_IA:
            i = (v >> 4) * 17
            out = np.stack((i, i, i, (v & 0xF) * 17), axis=-1)
        else:
            out = np.stack((v, v, v, v), axis=-1)
    elif siz == G_IM_SIZ_16b:
        a = ((row + xs * 2) ^ sw) & 0xFFE
        v = (T[a].astype(np.uint32) << 8) | T[a + 1]
        if fmt == G_IM_FMT_IA:
            out = conv16(v, ia=True)
        elif fmt == G_IM_FMT_CI:
            out = pal_rgba(v >> 8)
        else:
            out = conv16(v)
    else:
        a = ((row + xs * 2) ^ sw) & 0x7FE
        out = np.stack((T[a], T[a + 1], T[0x800 + a], T[0x800 + a + 1]), axis=-1).astype(np.uint32)
    flat = out.reshape(-1, 4).astype(np.int64).tolist()
    return [tuple(c) for c in flat]


def _emit_wrap(dst: str, src: str, axis: str, i: int, mode) -> List[str]:
    """Inline integer texel wrap for one axis: clamp, mirror, mask (+ modulo if the decode was capped)."""
    clamp, mirror, masked, capped = mode
    M, MB, HI, N = f"M{axis}{i}", f"MB{axis}{i}", f"HI{axis}{i}", f"N{axis}{i}"
    out = []
    v = src
    if clamp:
        out.append(f"{dst} = 0 if {v} < 0 else ({HI} if {v} > {HI} else {v})")
        v = dst
    if masked:
        if mirror:
            out.append(f"{dst} = (~{v} if {v} & {MB} else {v}) & {M}")
        else:
            out.append(f"{dst} = {v} & {M}")
        v = dst
    if v != dst:
        out.append(f"{dst} = {v}")
    if capped:
        out.append(f"{dst} %= {N}")
    return out


def _emit_sample(prefix: str, i: int, modes, bilerp: bool) -> List[str]:
    """Inline point / bilinear fetch from decoded texels TX{i} (row width W{i})."""
    mx, my = modes
    L = []
    if not bilerp:
        L.append(f"_fx = ss * SCS{i} - SL{i}; _ix = int(_fx); _ix -= _fx < _ix")
        L.append(f"_fy = tt * SCT{i} - TL{i}; _iy = int(_fy); _iy -= _fy < _iy")
        L += _emit_wrap("_xa", "_ix", "X", i, mx)
        L += _emit_wrap("_ya", "_iy", "Y", i, my)
        L.append(f"{prefix}r, {prefix}g, {prefix}b, {prefix}a = TX{i}[_ya * W{i} + _xa]")
        return L
    # RDP bilinear: base texel = floor(s), fraction = s - floor(s) — no half-texel shift (unlike GL).
    L.append(f"_fx = ss * SCS{i} - SL{i}; _ix = int(_fx); _ix -= _fx < _ix; _ux = _fx - _ix")
    L.append(f"_fy = tt * SCT{i} - TL{i}; _iy = int(_fy); _iy -= _fy < _iy; _uy = _fy - _iy")
    L.append("_ix1 = _ix + 1; _iy1 = _iy + 1")
    L += _emit_wrap("_xa", "_ix", "X", i, mx)
    L += _emit_wrap("_xb", "_ix1", "X", i, mx)
    L += _emit_wrap("_ya", "_iy", "Y", i, my)
    L += _emit_wrap("_yb", "_iy1", "Y", i, my)
    L.append(f"_ra = _ya * W{i}; _rb = _yb * W{i}")
    L.append(f"_c00 = TX{i}[_ra + _xa]; _c10 = TX{i}[_ra + _xb]; _c01 = TX{i}[_rb + _xa]; _c11 = TX{i}[_rb + _xb]")
    L.append("_w11 = _ux * _uy; _w10 = _ux - _w11; _w01 = _uy - _w11; _w00 = 1.0 - _ux - _uy + _w11")
    for k, ch in enumerate("rgba"):
        L.append(f"{prefix}{ch} = _c00[{k}] * _w00 + _c10[{k}] * _w10 + _c01[{k}] * _w01 + _c11[{k}] * _w11")
    return L


FRAMESKIP_CHOICES = ("off", "auto", "1", "2")


def normalize_frameskip(v) -> str:
    v = str(v).strip().lower()
    return v if v in FRAMESKIP_CHOICES else "off"


# ── numpy whole-triangle rasterizer (translated from the generated scalar span code) ──
NP_TRI_MIN_PIXELS = 128      # smaller triangles/batches stay on the scalar spans (numpy setup cost)
NP_BATCH_MAX_PIXELS = 65536  # cap on pixels per batched numpy pass


class _NpFallback(Exception):
    """Raised inside a numpy triangle when the scalar span would behave differently (or fail)."""


def _np_trunc(v):
    """``int(v)`` elementwise: truncate toward zero; refuse values Python would treat differently."""
    a = _np.asarray(v)
    if a.dtype.kind in "iub":
        return a.astype(_np.int64)
    if not _np.all(_np.isfinite(a)) or (a.size and float(_np.abs(a).max()) >= 2.0 ** 52):
        raise _NpFallback
    return _np.trunc(a).astype(_np.int64)


def _np_where(c, a, b):
    return _np.where(c, a, b)


def _np_not(c):
    return _np.logical_not(c)


def _np_or(*cs):
    out = cs[0]
    for c in cs[1:]:
        out = _np.logical_or(out, c)
    return out


def _np_and(*cs):
    out = cs[0]
    for c in cs[1:]:
        out = _np.logical_and(out, c)
    return out


def _np_divw(ic):
    """``1.0 / ic if ic else 0.0`` elementwise."""
    nz = ic != 0
    return _np.where(nz, 1.0 / _np.where(nz, ic, 1.0), 0.0)


_NP_TX_CACHE: Dict[int, Any] = {}


def _np_texels(tx):
    """Decoded texel list → (N, 4) int64 array (cached per decoded texture object)."""
    if tx is None:
        return None
    hit = _NP_TX_CACHE.get(id(tx))
    if hit is not None and hit[0] is tx:
        return hit[1]
    if len(_NP_TX_CACHE) > 512:
        _NP_TX_CACHE.clear()
    arr = _np.array(tx, dtype=_np.int64).reshape(-1, 4) if len(tx) else _np.zeros((0, 4), dtype=_np.int64)
    _NP_TX_CACHE[id(tx)] = (tx, arr)
    return arr


_Z_DECODE_NP = None
_Z_ENCODE_NP = None


def _np_tri_translate(body: List[str], prim_z_src: bool) -> Optional[List[str]]:
    """Translate scalar span statements to whole-triangle numpy statements; None if unsupported.

    ``continue`` becomes a pixel mask ``M``; RDRAM writes are collected in ``PEND``.
    """
    import re
    clamp_re = re.compile(r"^(\w+) = 0 if (\w+) < 0 else \((\w+) if \2 > \3 else \2\)$")
    mirror_re = re.compile(r"\(~(\w+) if \1 & (\w+) else \1\)")
    setif_re = re.compile(r"^if (\w+) (<=|<|>=|>|==) (\w+): (\w+) = (\w+)$")
    aug_re = re.compile(r"^(\w+) (\+|-|%|&|\|)= (.+)$")
    rd16_re = re.compile(r"\(rd\[(\w+)\] << 8\) \| rd\[\1 \+ 1\]")
    rdw_re = re.compile(r"^rd\[([^\]]+)\] = (.+)$")
    out: List[str] = []
    defined = ["Y", "x", "zc", "ic", "sc", "tc", "sr", "sg", "sb", "sa", "rowc", "rowz"]
    compacted = False
    for line in body:
        if line.startswith(("zc = z;", "sr = r;")) or line == "n += 1":
            continue
        if line == "zv = PZ if PZS else int(zc)":
            out.append("zv = _np_full(Y.shape[0], PZ)" if prim_z_src else "zv = TRUNC(zc)")
            defined.append("zv")
            continue
        m = re.match(r"^if (.+): continue$", line)
        if m:
            cond = m.group(1)
            if " if " in cond:
                return None
            if " or " in cond:
                cond = "OR(" + ", ".join(f"({c})" for c in cond.split(" or ")) + ")"
            elif " and " in cond:
                cond = "AND(" + ", ".join(f"({c})" for c in cond.split(" and ")) + ")"
            out.append(f"M = AND(M, NOT({cond}))")
            if not compacted:
                # Drop rejected pixels once (usually the depth test) so later stages do less work.
                compacted = True
                names = list(dict.fromkeys(defined))
                out.append("_k = M.nonzero()[0]")
                out.append(", ".join(names) + " = " + ", ".join(f"CMP({n}, _k)" for n in names))
                out.append("M = M[_k]")
            continue
        m = setif_re.match(line)
        if m:
            out.append(f"{m.group(4)} = WHERE({m.group(1)} {m.group(2)} {m.group(3)}, {m.group(5)}, {m.group(4)})")
            continue
        if line == "_w = 1.0 / ic if ic else 0.0":
            out.append("_w = DIVW(ic)")
            defined.append("_w")
            continue
        for st in line.split("; "):
            m = clamp_re.match(st)
            if m:
                d, v, hi = m.groups()
                out.append(f"{d} = WHERE({v} < 0, 0, WHERE({v} > {hi}, {hi}, {v}))")
                defined.append(d)
                continue
            st = mirror_re.sub(lambda mm: f"WHERE(({mm.group(1)} & {mm.group(2)}) != 0, ~{mm.group(1)}, {mm.group(1)})", st)
            st = st.replace("int(", "TRUNC(")
            m = rdw_re.match(st)
            if m:
                out.append(f"PEND.append(({m.group(1)}, {m.group(2)}))")
                continue
            m = aug_re.match(st)
            if m:
                st = f"{m.group(1)} = {m.group(1)} {m.group(2)} ({m.group(3)})"
            st = rd16_re.sub(lambda mm: f"RD16({mm.group(1)})", st)
            st = re.sub(r"rd\[([^\]]+)\]", r"RDI(\1)", st)
            st = st.replace("ZD[", "ZDN[").replace("ZE[", "ZEN[")
            st = re.sub(r"\bTX(\d)\[", r"TXN\1[", st)
            st = re.sub(r"\b(_c\d\d)\[(\d)\]", r"\1[:, \2]", st)
            if re.match(r"^\w+, \w+, \w+, \w+ = TXN\d\[", st):
                st += ".T"
            if " if " in st or "continue" in st or "rd[" in st or "STATS" in st:
                return None
            lhs = st.split(" = ", 1)[0] if " = " in st else ""
            defined += [n.strip() for n in lhs.split(",") if n.strip().isidentifier()]
            out.append(st)
    return out


def _np_compact(a, k):
    return a[k] if isinstance(a, _np.ndarray) and a.ndim == 1 else a


def _build_tri_np(make_sig: str, body: List[str], prim_z_src: bool, env: Dict[str, Any]):
    """Compile ``make(...) -> tri(Y, x, zc, ic, sc, tc, sr, sg, sb, sa) -> (mask, pending writes)``."""
    global _Z_DECODE_NP, _Z_ENCODE_NP
    stmts = _np_tri_translate(body, prim_z_src)
    if stmts is None:
        return None
    if _Z_DECODE_NP is None:
        _Z_DECODE_NP = _np.array(_Z_DECODE, dtype=_np.int64)
        _Z_ENCODE_NP = _np.array(_Z_ENCODE, dtype=_np.int64)
    src = [make_sig,
           " TXN0 = NPTX(TX0); TXN1 = NPTX(TX1); RD = rd",
           " def RD16(a): return (RD[a].astype(INT64) << 8) | RD[a + 1]",
           " def RDI(a): return RD[a].astype(INT64)",
           " def tri(Y, x, zc, ic, sc, tc, sr, sg, sb, sa):",
           "  rowc = cimg + Y * cstride",
           "  rowz = zimg + Y * zstride",
           "  M = _np_full(Y.shape[0], True)",
           "  PEND = []"]
    src += ["  " + st for st in stmts]
    src += ["  return M, PEND", " return tri"]
    nenv = dict(env)
    nenv.update({"CMP": _np_compact, "TRUNC": _np_trunc, "WHERE": _np_where, "NOT": _np_not, "OR": _np_or, "AND": _np_and,
                 "DIVW": _np_divw, "NPTX": _np_texels, "INT64": _np.int64, "_np_full": _np.full,
                 "ZDN": _Z_DECODE_NP, "ZEN": _Z_ENCODE_NP})
    ns: Dict[str, Any] = {}
    try:
        exec(compile("\n".join(src), "<rdp-tri-np>", "exec"), nenv, ns)
    except SyntaxError:
        return None
    import re
    text = "\n".join(stmts)
    make = ns["make"]
    # Which of (zc, ic, sc, tc, sr, sg, sb, sa) the statements actually read; unused planes are skipped.
    make.planes_used = tuple(bool(re.search(rf"\b{n}\b", text)) for n in ("zc", "ic", "sc", "tc", "sr", "sg", "sb", "sa"))
    return make


class RdpTile:
    __slots__ = ("fmt", "siz", "line", "tmem", "pal", "cmt", "maskt", "shiftt", "cms", "masks", "shifts",
                 "sl", "tl", "sh", "th")

    def __init__(self):
        self.fmt = self.siz = self.line = self.tmem = self.pal = 0
        self.cmt = self.maskt = self.shiftt = self.cms = self.masks = self.shifts = 0
        self.sl = self.tl = self.sh = self.th = 0


class SoftRDP:
    """N64 RDP in software. Draws straight into emulated RDRAM so CPU readback works."""

    def __init__(self, core):
        self.core = core
        self.tmem = bytearray(4096)
        self.tmem_version = 0
        self._tex_cache: Dict[Any, Any] = {}
        self._span_cache: Dict[Any, Any] = {}
        self.fs_skip = False   # frame-skip: drop rasterization for this frame (state still updates)
        self.stats = {"tris": 0, "pixels": 0, "rects": 0}
        self._span_bound = None
        self._batch = None       # pending pixel-disjoint triangles sharing one bound state
        self._batching = False   # only inside GfxHLE.run_task (direct callers draw immediately)
        self.reset()

    def reset(self):
        self._batch = None
        self.cimg = 0; self.cfmt = 0; self.csiz = G_IM_SIZ_16b; self.cwidth = 320
        self.zimg = 0
        self.timg = 0; self.tfmt = 0; self.tsiz = 0; self.twidth = 1
        self.scissor = (0, 0, 320, 240)
        self.omh = 0; self.oml = 0
        self.combine = (0, 0)
        self.fill_color = 0
        self.fog = (0, 0, 0, 0); self.blend = (0, 0, 0, 0)
        self.prim = (255, 255, 255, 255); self.env = (255, 255, 255, 255)
        self.prim_lod_frac = 0; self.prim_z = 0
        self.key = (0, 0, 0)
        self.tiles = [RdpTile() for _ in range(8)]
        self._tex_cache.clear()

    # ── state commands ──
    @property
    def cycle_type(self) -> int:
        return (self.omh >> 20) & 3

    def set_color_image(self, fmt, siz, width, addr):
        self.cfmt, self.csiz, self.cwidth, self.cimg = fmt, siz, max(1, width), addr & 0xFFFFFF
        hook = getattr(self.core, "_fs_on_cimg", None)
        if hook is not None:
            hook(self.cimg, self.cwidth * self._fb_bpp())

    def set_texture_image(self, fmt, siz, width, addr):
        self.tfmt, self.tsiz, self.twidth, self.timg = fmt, siz, max(1, width), addr & 0xFFFFFF

    def set_tile(self, w0, w1):
        t = self.tiles[(w1 >> 24) & 7]
        t.fmt = (w0 >> 21) & 7; t.siz = (w0 >> 19) & 3; t.line = (w0 >> 9) & 0x1FF; t.tmem = w0 & 0x1FF
        t.pal = (w1 >> 20) & 0xF; t.cmt = (w1 >> 18) & 3; t.maskt = (w1 >> 14) & 0xF; t.shiftt = (w1 >> 10) & 0xF
        t.cms = (w1 >> 8) & 3; t.masks = (w1 >> 4) & 0xF; t.shifts = w1 & 0xF

    def set_tile_size(self, w0, w1):
        t = self.tiles[(w1 >> 24) & 7]
        t.sl = (w0 >> 12) & 0xFFF; t.tl = w0 & 0xFFF; t.sh = (w1 >> 12) & 0xFFF; t.th = w1 & 0xFFF

    def _touch_tmem(self):
        self.tmem_version += 1
        if len(self._tex_cache) > 1024:
            self._tex_cache.clear()

    def load_block(self, w0, w1):
        """LoadBlock: linear copy into TMEM; dxt decides which 64-bit words are on odd lines."""
        self._flush_batch()
        tile = self.tiles[(w1 >> 24) & 7]
        sl = (w0 >> 12) & 0xFFF; tl = w0 & 0xFFF; sh = (w1 >> 12) & 0xFFF; dxt = w1 & 0xFFF
        siz = self.tsiz
        bpt = (1 << siz) >> 1 if siz else 0  # bytes per texel (4b → 0, handled as half)
        texels = sh - sl + 1
        nbytes = (texels << siz) >> 1
        src = self.timg + (((tl * self.twidth + sl) << siz) >> 1)
        rd = self.core.rdram
        tm = self.tmem
        base = (tile.tmem << 3) & 0xFFF
        nwords = (nbytes + 7) >> 3
        tcount = 0
        for i in range(nwords):
            off = src + i * 8
            word = rd[off:off + 8] if off + 8 <= len(rd) else bytes(8)
            if (tcount >> 11) & 1:
                word = bytes(word[4:8]) + bytes(word[0:4])
            dst = (base + i * 8) & 0xFFF
            if siz == G_IM_SIZ_32b:
                # RGBA32 is split: RG halves in low TMEM, BA halves in high TMEM.
                d = (base + i * 4) & 0x7FF
                tm[d:d + 2] = word[0:2]; tm[d + 2:d + 4] = word[4:6]
                tm[0x800 + d:0x800 + d + 2] = word[2:4]; tm[0x800 + d + 2:0x800 + d + 4] = word[6:8]
            else:
                tm[dst:dst + 8] = word
            tcount += dxt
        self._touch_tmem()

    def load_tile(self, w0, w1):
        """LoadTile: copy a rectangle row by row; odd TMEM rows are 32-bit word swapped."""
        self._flush_batch()
        tile = self.tiles[(w1 >> 24) & 7]
        sl = ((w0 >> 12) & 0xFFF) >> 2; tl = (w0 & 0xFFF) >> 2
        sh = ((w1 >> 12) & 0xFFF) >> 2; th = (w1 & 0xFFF) >> 2
        siz = self.tsiz
        rd = self.core.rdram; tm = self.tmem
        width = sh - sl + 1
        row_bytes = (width << siz) >> 1
        line = tile.line << 3
        base = tile.tmem << 3
        for row in range(th - tl + 1):
            src = self.timg + ((((tl + row) * self.twidth + sl) << siz) >> 1)
            data = rd[src:src + row_bytes]
            if siz == G_IM_SIZ_32b:
                d0 = (base + row * line) & 0x7FF
                for i in range(0, len(data) - 3, 4):
                    j = i >> 1
                    a = (d0 + j) ^ (4 if row & 1 else 0)
                    tm[a & 0x7FF:(a & 0x7FF) + 2] = data[i:i + 2]
                    tm[0x800 + (a & 0x7FF):0x800 + (a & 0x7FF) + 2] = data[i + 2:i + 4]
                continue
            dst = base + row * line
            for i in range(0, len(data), 4):
                a = (dst + i) ^ (4 if row & 1 else 0)
                tm[a & 0xFFF:(a & 0xFFF) + 4] = data[i:i + 4].ljust(4, b"\0")[:4]
        self._touch_tmem()

    def load_tlut(self, w0, w1):
        """LoadTLUT: 16-bit palette entries, each quadricated into 8 bytes of high TMEM."""
        self._flush_batch()
        tile = self.tiles[(w1 >> 24) & 7]
        sl = ((w0 >> 12) & 0xFFF) >> 2; tl = (w0 & 0xFFF) >> 2
        sh = ((w1 >> 12) & 0xFFF) >> 2
        rd = self.core.rdram; tm = self.tmem
        src = self.timg + ((tl * self.twidth + sl) << 1)
        base = tile.tmem << 3
        for i in range(sh - sl + 1):
            v = rd[src + i * 2:src + i * 2 + 2]
            if len(v) < 2:
                break
            d = (base + i * 8) & 0xFFF
            tm[d:d + 8] = bytes(v) * 4
        self._touch_tmem()

    # ── texture decoding ──
    def _decode_tile(self, ti: int):
        """Decode a tile's TMEM texels into a flat list of RGBA tuples (cached by TMEM version)."""
        t = self.tiles[ti]
        tlut = (self.omh >> 14) & 3
        # Indices reaching the decoder are < 1<<mask when masked, else < the tile size.
        w = (1 << t.masks) if t.masks else max(1, ((t.sh - t.sl) >> 2) + 1)
        h = (1 << t.maskt) if t.maskt else max(1, ((t.th - t.tl) >> 2) + 1)
        w = min(w, 256); h = min(h, 256)
        tm = self.tmem
        line = t.line << 3
        base = t.tmem << 3
        # Key on the TMEM bytes actually addressed (+ palette), so re-loading the same texture hits.
        span = max(line * h, ((w << t.siz) >> 1) + 8)
        if base + span <= 0x1000:
            region = bytes(tm[base:base + span])
        else:
            region = bytes(tm[base:]) + bytes(tm[:(base + span) & 0xFFF])
        if t.siz == G_IM_SIZ_32b:
            region += bytes(tm[0x800 + (base & 0x7FF):0x800 + (base & 0x7FF) + span])
        pal = bytes(tm[0x800:0x1000]) if (t.fmt == G_IM_FMT_CI or tlut) and t.siz <= G_IM_SIZ_8b else b""
        if pal and t.siz == G_IM_SIZ_4b:
            pal = pal[t.pal * 128:t.pal * 128 + 128]
        key = (t.fmt, t.siz, t.line, t.pal, w, h, tlut, region, pal)
        hit = self._tex_cache.get(key)
        if hit is not None:
            return hit
        if USE_NUMPY and _np is not None:
            out = _np_decode_tile(tm, base, line, w, h, t.fmt, t.siz, t.pal, tlut)
            if out is not None:
                res = (out, w, h)
                self._tex_cache[key] = res
                return res
        fmt, siz = t.fmt, t.siz
        out = [None] * (w * h)
        pal_fn = _ia16 if tlut == 3 else _rgba5551
        for y in range(h):
            row = base + y * line
            sw = 4 if y & 1 else 0
            for x in range(w):
                if siz == G_IM_SIZ_4b:
                    a = ((row + (x >> 1)) ^ sw) & 0xFFF
                    v = (tm[a] >> 4) if not (x & 1) else (tm[a] & 0xF)
                    if fmt == G_IM_FMT_CI or (tlut and fmt != G_IM_FMT_IA and fmt != G_IM_FMT_I):
                        e = 0x800 + (((t.pal << 4) | v) << 3)
                        c = pal_fn((tm[e] << 8) | tm[e + 1])
                    elif fmt == G_IM_FMT_IA:
                        i = (v >> 1) * 255 // 7
                        c = (i, i, i, 255 if v & 1 else 0)
                    else:
                        i = v * 17
                        c = (i, i, i, i)
                elif siz == G_IM_SIZ_8b:
                    a = ((row + x) ^ sw) & 0xFFF
                    v = tm[a]
                    if fmt == G_IM_FMT_CI or (tlut and fmt == G_IM_FMT_RGBA):
                        e = 0x800 + (v << 3)
                        c = pal_fn((tm[e & 0xFFF] << 8) | tm[(e + 1) & 0xFFF])
                    elif fmt == G_IM_FMT_IA:
                        i = (v >> 4) * 17
                        c = (i, i, i, (v & 0xF) * 17)
                    else:
                        c = (v, v, v, v)
                elif siz == G_IM_SIZ_16b:
                    a = ((row + x * 2) ^ sw) & 0xFFE
                    v = (tm[a] << 8) | tm[a + 1]
                    if fmt == G_IM_FMT_IA:
                        c = _ia16(v)
                    elif fmt == G_IM_FMT_CI:
                        e = 0x800 + ((v >> 8) << 3)
                        c = pal_fn((tm[e & 0xFFF] << 8) | tm[(e + 1) & 0xFFF])
                    else:
                        c = _rgba5551(v)
                else:  # 32-bit RGBA: RG in low half, BA in high half
                    a = ((row + x * 2) ^ sw) & 0x7FE
                    c = (tm[a], tm[a + 1], tm[0x800 + a], tm[0x800 + a + 1])
                out[y * w + x] = c
        res = (out, w, h)
        self._tex_cache[key] = res
        return res

    def _tile_params(self, ti: int):
        """(mode_key, values) for inline sampling of tile ti; values bind into span factories."""
        t = self.tiles[ti & 7]
        texels, w, h = self._decode_tile(ti & 7)
        cw = max(1, ((t.sh - t.sl) >> 2) + 1); ch = max(1, ((t.th - t.tl) >> 2) + 1)
        def sc(shift):
            if not shift:
                return 1.0
            return 1.0 / (1 << shift) if shift <= 10 else float(1 << (16 - shift))
        def axis(mask, cm, clampn, n):
            clamp = bool(cm & 2) or not mask
            mirror = bool(cm & 1) and bool(mask)
            m = (1 << mask) - 1 if mask else 0
            capped = (mask and (1 << mask) > n) or (not mask and clampn > n)
            return (clamp, mirror, bool(mask), bool(capped)), (m, (1 << mask) if mask else 0, clampn - 1, n)
        kx, vx = axis(t.masks, t.cms, cw, w)
        ky, vy = axis(t.maskt, t.cmt, ch, h)
        values = (texels, w, sc(t.shifts), sc(t.shiftt), t.sl / 4.0, t.tl / 4.0) + vx + vy
        return (kx, ky), values

    def _sampler(self, ti: int, bilerp: bool):
        """Return sample(s, t) → (r,g,b,a); s,t are texel coordinates (float, tile space)."""
        t = self.tiles[ti]
        texels, w, h = self._decode_tile(ti)
        sl = t.sl / 4.0; tl = t.tl / 4.0
        cw = max(1, ((t.sh - t.sl) >> 2) + 1); ch = max(1, ((t.th - t.tl) >> 2) + 1)

        def axis(shift, mask, cm, clampn, n):
            """Specialised integer wrap for one axis: clamp, then mirror/mask, then fit the decode."""
            scale = 1.0
            if shift:
                scale = 1.0 / (1 << shift) if shift <= 10 else float(1 << (16 - shift))
            clamp = bool(cm & 2) or not mask
            mirror = bool(cm & 1) and mask
            m = (1 << mask) - 1 if mask else 0
            mb = 1 << mask if mask else 0
            hi = clampn - 1
            if clamp and not mask:
                fn = lambda v: (0 if v < 0 else (hi if v > hi else v)) % n
            elif clamp and mirror:
                fn = lambda v: ((~(0 if v < 0 else (hi if v > hi else v))) if ((0 if v < 0 else (hi if v > hi else v)) & mb) else (0 if v < 0 else (hi if v > hi else v))) & m
            elif clamp:
                fn = lambda v: (0 if v < 0 else (hi if v > hi else v)) & m
            elif mirror:
                fn = lambda v: ((~v) if v & mb else v) & m
            else:
                fn = lambda v: v & m
            return scale, fn

        scs, wx = axis(t.shifts, t.masks, t.cms, cw, w)
        sct, wy = axis(t.shiftt, t.maskt, t.cmt, ch, h)
        fl = math.floor
        if not bilerp:
            def sample(s, tt):
                return texels[(wy(fl(tt * sct - tl)) % h) * w + (wx(fl(s * scs - sl)) % w)]
            return sample

        def sample_bl(s, tt):
            fs = s * scs - sl; ft = tt * sct - tl
            x0 = fl(fs); y0 = fl(ft)
            fx = fs - x0; fy = ft - y0
            xa = wx(x0) % w; xb = wx(x0 + 1) % w
            ya = (wy(y0) % h) * w; yb = (wy(y0 + 1) % h) * w
            c00 = texels[ya + xa]; c10 = texels[ya + xb]; c01 = texels[yb + xa]; c11 = texels[yb + xb]
            w11 = fx * fy; w10 = fx - w11; w01 = fy - w11; w00 = 1.0 - fx - fy + w11
            return (int(c00[0] * w00 + c10[0] * w10 + c01[0] * w01 + c11[0] * w11),
                    int(c00[1] * w00 + c10[1] * w10 + c01[1] * w01 + c11[1] * w11),
                    int(c00[2] * w00 + c10[2] * w10 + c01[2] * w01 + c11[2] * w11),
                    int(c00[3] * w00 + c10[3] * w10 + c01[3] * w01 + c11[3] * w11))
        return sample_bl

    # ── framebuffer helpers ──
    def _fb_bpp(self) -> int:
        return {G_IM_SIZ_8b: 1, G_IM_SIZ_16b: 2, G_IM_SIZ_32b: 4}.get(self.csiz, 2)

    def _clip_rect(self, x0, y0, x1, y1):
        sx0, sy0, sx1, sy1 = self.scissor
        return max(x0, sx0, 0), max(y0, sy0, 0), min(x1, sx1, self.cwidth), min(y1, sy1, 1024)

    def fill_rect(self, xl, yl, xh, yh):
        """Fill/1cyc/2cyc rectangle (coords 10.2). Fill/copy modes include the far edge."""
        self._flush_batch()
        if self.fs_skip:
            return
        self.stats["rects"] += 1
        ct = self.cycle_type
        x0 = xl >> 2; y0 = yl >> 2
        if ct in (G_CYC_FILL, G_CYC_COPY):
            x1 = (xh >> 2) + 1; y1 = (yh >> 2) + 1
        else:
            x1 = (xh + 3) >> 2; y1 = (yh + 3) >> 2
        x0, y0, x1, y1 = self._clip_rect(x0, y0, x1, y1)
        if x1 <= x0 or y1 <= y0:
            return
        rd = self.core.rdram
        bpp = self._fb_bpp()
        if ct == G_CYC_FILL:
            fc = self.fill_color & MASK_32
            stride = self.cwidth * bpp
            if bpp == 2:
                pat = struct.pack(">I", fc)
                for y in range(y0, y1):
                    row = self.cimg + y * stride
                    a = row + x0 * 2; b = row + x1 * 2
                    if b > len(rd): break
                    # Even pixels take the high half of the fill colour, odd pixels the low half.
                    seg = (pat * ((b - a) // 4 + 2))
                    off = (x0 & 1) * 2
                    rd[a:b] = seg[off:off + (b - a)]
            elif bpp == 4:
                pat = struct.pack(">I", fc)
                for y in range(y0, y1):
                    a = self.cimg + (y * self.cwidth + x0) * 4; n = x1 - x0
                    if a + n * 4 > len(rd): break
                    rd[a:a + n * 4] = pat * n
            else:
                for y in range(y0, y1):
                    a = self.cimg + y * self.cwidth + x0; n = x1 - x0
                    if a + n > len(rd): break
                    rd[a:a + n] = bytes([(fc >> (24 - ((x & 3) << 3))) & 0xFF for x in range(x0, x1)])
            return
        # 1/2-cycle rectangle: flat primitive with shade = 0, no texture.
        self._raster_rect(x0, y0, x1, y1, None)

    def tex_rect(self, tile, xl, yl, xh, yh, s, t, dsdx, dtdy, flip=False):
        self._flush_batch()
        if self.fs_skip:
            return
        """Texture rectangle: coords 10.2, s/t s10.5, dsdx/dtdy s5.10."""
        self.stats["rects"] += 1
        ct = self.cycle_type
        x0 = xl >> 2; y0 = yl >> 2
        if ct in (G_CYC_FILL, G_CYC_COPY):
            x1 = (xh >> 2) + 1; y1 = (yh >> 2) + 1
            if ct == G_CYC_COPY:
                dsdx /= 4.0  # copy mode moves 4 texels per clock
        else:
            x1 = (xh + 3) >> 2; y1 = (yh + 3) >> 2
        cx0, cy0, cx1, cy1 = self._clip_rect(x0, y0, x1, y1)
        if cx1 <= cx0 or cy1 <= cy0:
            return
        s0 = s / 32.0 + (cx0 - x0) * (dsdx / 1024.0)
        t0 = t / 32.0 + (cy0 - y0) * (dtdy / 1024.0)
        if flip:
            s0 = s / 32.0 + (cy0 - y0) * (dsdx / 1024.0)
            t0 = t / 32.0 + (cx0 - x0) * (dtdy / 1024.0)
        self._raster_rect(cx0, cy0, cx1, cy1, (tile, s0, t0, dsdx / 1024.0, dtdy / 1024.0, flip))

    def _raster_rect(self, x0, y0, x1, y1, tex):
        z = self.prim_z << 3
        fn = self._span_fn(tex[0] if tex else 0, rect=True)
        for y in range(y0, y1):
            if tex is None:
                fn(y, x0, x1, z, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
                continue
            tile, s0, t0, ds, dt, flip = tex
            if flip:  # s steps down the rows, t across the columns
                fn(y, x0, x1, z, 0.0, 1.0, 0.0, s0 + (y - y0) * ds, 0.0, t0, dt,
                   0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)
            else:
                fn(y, x0, x1, z, 0.0, 1.0, 0.0, s0, ds, t0 + (y - y0) * dt, 0.0,
                   0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0)

    # ── triangles ──
    def draw_triangle(self, v0, v1, v2, tile: int, textured: bool, shade_smooth: bool = True):
        """v = (x, y, z18, invw, s/w, t/w, r, g, b, a) in screen space; s,t in texels."""
        if self.fs_skip:
            return
        self.stats["tris"] += 1
        x0, y0 = v0[0], v0[1]; x1, y1 = v1[0], v1[1]; x2, y2 = v2[0], v2[1]
        area = (x1 - x0) * (y2 - y0) - (x2 - x0) * (y1 - y0)
        if abs(area) < 1e-6:
            return
        sx0, sy0, sx1, sy1 = self._clip_rect(0, 0, 4096, 4096)
        miny = max(sy0, int(math.floor(min(y0, y1, y2) + 0.5)))
        maxy = min(sy1 - 1, int(math.ceil(max(y0, y1, y2) - 0.5)))
        if maxy < miny:
            return
        inv = 1.0 / area
        # Attribute plane equations: f(x,y) = f0 + dfdx*(x-x0) + dfdy*(y-y0)
        def plane(i):
            f0, f1, f2 = v0[i], v1[i], v2[i]
            dfdx = ((f1 - f0) * (y2 - y0) - (f2 - f0) * (y1 - y0)) * inv
            dfdy = ((f2 - f0) * (x1 - x0) - (f1 - f0) * (x2 - x0)) * inv
            return f0, dfdx, dfdy
        if not shade_smooth:
            # Flat shading uses the first vertex's colour.
            v1 = v1[:6] + v0[6:10]; v2 = v2[:6] + v0[6:10]
        planes = [plane(i) for i in range(2, 10)]
        fn = self._span_fn(tile if textured else 0, rect=False)
        edges = ((x0, y0, x1, y1), (x1, y1, x2, y2), (x2, y2, x0, y0))
        ceil = math.ceil
        rows = []
        npx = 0
        for y in range(miny, maxy + 1):
            py = y + 0.5
            xl = 1e9; xr = -1e9
            for ax, ay, bx, by in edges:
                if (ay <= py < by) or (by <= py < ay):
                    xi = ax + (py - ay) * (bx - ax) / (by - ay)
                    if xi < xl: xl = xi
                    if xi > xr: xr = xi
            if xr < xl:
                continue
            xs = int(ceil(xl - 0.5))
            if xs < sx0: xs = sx0
            xe = int(ceil(xr - 0.5))
            if xe > sx1: xe = sx1
            if xe <= xs:
                continue
            rows.append((y, xs, xe))
            npx += xe - xs
        if not rows:
            return
        bound = self._span_bound
        if USE_NUMPY and _np is not None and bound is not None and bound[0][5] is not None:
            tri = (rows, planes, x0, y0, fn)
            if self._batching:
                self._batch_add(bound, tri, npx)
                return
            # Big triangles: rasterize the whole triangle at once with numpy (bit-identical output).
            if npx >= NP_TRI_MIN_PIXELS and self._raster_np(bound[0], bound[1], [tri]):
                return
        for y, xs, xe in rows:
            py = y + 0.5
            px = xs + 0.5
            vals = []
            for f0, dx, dy in planes:
                vals.append(f0 + dx * (px - x0) + dy * (py - y0))
                vals.append(dx)
            fn(y, xs, xe, *vals)

    # ── triangle batching: pixel-disjoint triangles with the same bound state commute ──
    def _batch_add(self, bound, tri, npx: int):
        entry, args = bound
        b = self._batch
        if b is not None and (b[0] is not entry or b[4] + npx > NP_BATCH_MAX_PIXELS or b[1] != args
                              or self._batch_overlaps(b[3], tri[0])):
            self._flush_batch()
            b = None
        if b is None:
            b = self._batch = [entry, args, [], {}, 0]
        b[2].append(tri)
        cov = b[3]
        for y, xs, xe in tri[0]:
            lst = cov.get(y)
            if lst is None:
                cov[y] = [(xs, xe)]
            else:
                lst.append((xs, xe))
        b[4] += npx

    @staticmethod
    def _batch_overlaps(cov, rows) -> bool:
        for y, xs, xe in rows:
            lst = cov.get(y)
            if lst:
                for a, c in lst:
                    if xs < c and a < xe:
                        return True
        return False

    def _flush_batch(self):
        """Draw pending batched triangles (numpy when worthwhile, else the scalar spans in order)."""
        b = self._batch
        if b is None:
            return
        self._batch = None
        entry, args, tris, _cov, npx = b
        if npx >= NP_TRI_MIN_PIXELS and self._raster_np(entry, args, tris):
            return
        for rows, planes, x0, y0, fn in tris:
            for y, xs, xe in rows:
                py = y + 0.5
                px = xs + 0.5
                vals = []
                for f0, dx, dy in planes:
                    vals.append(f0 + dx * (px - x0) + dy * (py - y0))
                    vals.append(dx)
                fn(y, xs, xe, *vals)

    def _raster_np(self, entry, args, tris) -> bool:
        """Numpy version of the bound span function over whole triangles; False = use the scalar spans.

        ``tris`` must be pixel-disjoint (a batch) so evaluation order cannot matter. Attributes step
        with a sequential ``np.add.accumulate`` per row, which reproduces the span's ``z += dz``
        float sequence exactly. Writes are deferred until every pixel has been validated, so a
        fallback never leaves a half-drawn batch behind.
        """
        np = _np
        used = entry[5].planes_used
        ys_l: List[int] = []; xs_l: List[int] = []; w_l: List[int] = []
        x0_l: List[float] = []; y0_l: List[float] = []
        pl_l: List[List[Any]] = [[] for _ in range(8)]
        for rows, planes, x0, y0, _fn in tris:
            nrow = len(rows)
            for y, xs, xe in rows:
                ys_l.append(y); xs_l.append(xs); w_l.append(xe - xs)
            x0_l += [x0] * nrow; y0_l += [y0] * nrow
            for k in range(8):
                if used[k]:
                    pl_l[k] += [planes[k]] * nrow
        nr = len(ys_l)
        ys = np.array(ys_l, dtype=np.int64)
        xs = np.array(xs_l, dtype=np.int64)
        w = np.array(w_l, dtype=np.int64)
        rd = self.core.rdram
        cimg, cstride, zimg, zstride = args[1], args[2], args[3], args[4]
        if zimg:
            ylo = int(ys.min()); yhi = int(ys.max()) + 1
            if cimg + ylo * cstride < zimg + yhi * zstride and zimg + ylo * zstride < cimg + yhi * cstride:
                return False  # colour and depth images alias: per-pixel order matters
        width = int(w.max())
        cols = np.arange(width)
        mask2 = cols[None, :] < w[:, None]
        px = xs + 0.5
        py = ys + 0.5
        X0 = np.array(x0_l, dtype=np.float64); Y0 = np.array(y0_l, dtype=np.float64)
        live = [k for k in range(8) if used[k]]
        attrs: List[Any] = [None] * 8
        with np.errstate(all="ignore"):
            if live:
                # One sequential accumulate over all used planes reproduces each span's `v += dv`.
                acc = np.empty((len(live), nr, width))
                for n_, k in enumerate(live):
                    P = np.array(pl_l[k], dtype=np.float64)   # rows × (f0, dx, dy)
                    acc[n_, :, 0] = P[:, 0] + P[:, 1] * (px - X0) + P[:, 2] * (py - Y0)
                    acc[n_, :, 1:] = P[:, 1:2]
                np.add.accumulate(acc, axis=2, out=acc)
                flat = acc[:, mask2]
                for n_, k in enumerate(live):
                    attrs[k] = flat[n_]
            X = (xs[:, None] + cols[None, :])[mask2]
            Y = np.repeat(ys, w)
            try:
                tri = entry[5](np.frombuffer(rd, dtype=np.uint8), *args[1:])
                M, pend = tri(Y, X, *attrs)
            except (_NpFallback, IndexError, ValueError, OverflowError, TypeError, ZeroDivisionError):
                return False
        n = int(np.count_nonzero(M))
        if n:
            limit = len(rd)
            writes = []
            for addr, val in pend:
                addr = np.broadcast_to(addr, M.shape)[M]
                val = np.broadcast_to(val, M.shape)[M]
                if val.dtype.kind not in "iub" or addr.dtype.kind not in "iu":
                    return False
                if int(addr.min()) < 0 or int(addr.max()) >= limit or int(val.min()) < 0 or int(val.max()) > 255:
                    return False
                writes.append((addr, val.astype(np.uint8)))
            RD = np.frombuffer(rd, dtype=np.uint8)
            for addr, val in writes:
                RD[addr] = val
            del RD
        self.stats["pixels"] += n
        return True

    def raw_triangle(self, words: List[int]):
        """RDP edge-coefficient triangle (commands 0x08-0x0F): words are 64-bit command words."""
        self._flush_batch()
        if self.fs_skip:
            return
        w0 = words[0]
        cmd = (w0 >> 56) & 0x3F
        lft = (w0 >> 55) & 1
        tile = (w0 >> 48) & 7
        def s14(v):
            v &= 0x3FFF
            return v - 0x4000 if v & 0x2000 else v
        yl = s14(w0 >> 32) / 4.0; ym = s14(w0 >> 16) / 4.0; yh = s14(w0) / 4.0
        def s32f(v):
            v &= MASK_32
            return (v - 0x100000000 if v & 0x80000000 else v) / 65536.0
        xl, dxl = s32f(words[1] >> 32), s32f(words[1])
        xh, dxh = s32f(words[2] >> 32), s32f(words[2])
        xm, dxm = s32f(words[3] >> 32), s32f(words[3])
        k = 4
        def attrs(base_word):
            """Four 16.16 values + their DxDx, DxDe, DxDy from an 8-word block."""
            def comb(iw, fw, idx):
                ip = (iw >> (48 - idx * 16)) & 0xFFFF
                fp = (fw >> (48 - idx * 16)) & 0xFFFF
                v = (ip << 16) | fp
                return (v - 0x100000000 if v & 0x80000000 else v) / 65536.0
            b = words[base_word:base_word + 8]
            out = []
            for idx in range(4):
                out.append((comb(b[0], b[2], idx), comb(b[1], b[3], idx), comb(b[4], b[6], idx), comb(b[5], b[7], idx)))
            return out
        shade = tex = None
        if cmd & 4:
            shade = attrs(k); k += 8
        if cmd & 2:
            tex = attrs(k); k += 8
        zc = None
        if cmd & 1:
            zw0 = words[k]; zw1 = words[k + 1]
            zc = (s32f(zw0 >> 32), s32f(zw0), s32f(zw1 >> 32), s32f(zw1))
        sx0, sy0, sx1, sy1 = self._clip_rect(0, 0, 4096, 4096)
        y_top = math.floor(yh)
        fn = self._span_fn(tile if tex else 0, rect=False)
        self.stats["tris"] += 1
        y = max(int(math.ceil(yh - 0.5)), sy0)
        y_end = min(int(math.ceil(yl - 0.5)), sy1)
        while y < y_end:
            py = y + 0.5
            dy = py - y_top
            x_major = xh + dxh * dy
            x_minor = (xm + dxm * dy) if py < ym else (xl + dxl * (py - ym))
            if lft:
                xa, xb = x_major, x_minor
            else:
                xa, xb = x_minor, x_major
            xs = max(sx0, int(math.ceil(xa - 0.5))); xe = min(sx1, int(math.ceil(xb - 0.5)))
            if xe > xs:
                ox = xs + 0.5 - x_major
                def at(v):
                    base, ddx, dde, _ddy = v
                    return base + dde * dy + ddx * ox, ddx
                if zc:
                    z0, dzx = at(zc)
                    z0 *= 8.0; dzx *= 8.0   # 15-bit integer depth → 18-bit internal
                else:
                    z0, dzx = float(self.prim_z << 3), 0.0
                if tex:
                    s0, dsx = at(tex[0]); t0, dtx = at(tex[1]); w0_, dwx = at(tex[2])
                    s0 /= 32.0; dsx /= 32.0; t0 /= 32.0; dtx /= 32.0
                    w0_ /= 32768.0; dwx /= 32768.0
                else:
                    s0 = dsx = t0 = dtx = 0.0; w0_, dwx = 1.0, 0.0
                if shade:
                    r0, drx = at(shade[0]); g0, dgx = at(shade[1]); b0, dbx = at(shade[2]); a0, dax = at(shade[3])
                else:
                    r0 = drx = g0 = dgx = b0 = dbx = a0 = dax = 0.0
                fn(y, xs, xe, z0, dzx, w0_, dwx, s0, dsx, t0, dtx, r0, drx, g0, dgx, b0, dbx, a0, dax)
            y += 1

    # ── span code generation ──
    def _span_fn(self, tile: int, rect: bool):
        """Span function for the current state: structural code is cached, values bound per draw."""
        base = (self.omh, self.oml, self.combine, rect, self.csiz, bool(self.zimg))
        probe = self._span_cache.get(base)
        if probe is None:
            if len(self._span_cache) > 1024:
                self._span_cache.clear()
            probe = self._build_span(tile, rect, None)   # discover texture usage
            self._span_cache[base] = probe
        uses_tex, uses_t1 = probe[1], probe[2]
        tp0 = tp1 = None
        if uses_tex:
            tp0 = self._tile_params(tile)
            tp1 = self._tile_params(tile + 1) if uses_t1 else tp0
            key = base + (tp0[0], tp1[0])
            entry = self._span_cache.get(key)
            if entry is None:
                entry = self._build_span(tile, rect, (tp0[0], tp1[0]))
                self._span_cache[key] = entry
        else:
            entry = probe
        make, uses_tex, uses_t1, bilerp, bpp = entry[:5]
        P = self.prim; E = self.env; BL = self.blend; FG = self.fog
        v0 = tp0[1] if tp0 else (None,) * 14
        v1 = tp1[1] if tp1 else (None,) * 14
        args = (self.core.rdram, self.cimg, self.cwidth * bpp, self.zimg, self.cwidth * 2,
                self.prim_z << 3, P[0], P[1], P[2], P[3], E[0], E[1], E[2], E[3],
                BL[0], BL[1], BL[2], BL[3], FG[0], FG[1], FG[2], FG[3], self.prim_lod_frac, *v0, *v1)
        self._span_bound = (entry, args)
        return make(*args)

    def _build_span(self, tile: int, rect: bool, tex_modes):
        omh, oml = self.omh, self.oml
        ct = (omh >> 20) & 3
        bpp = self._fb_bpp()
        persp = bool(omh & (1 << 19)) and not rect
        bilerp = ((omh >> 12) & 3) != 0 and ct != G_CYC_COPY
        w0c, w1c = self.combine
        # Decode combiner selectors (cycle 0 and 1).
        cyc = [
            dict(a=(w0c >> 20) & 0xF, c=(w0c >> 15) & 0x1F, Aa=(w0c >> 12) & 7, Ac=(w0c >> 9) & 7,
                 b=(w1c >> 28) & 0xF, Ab=(w1c >> 12) & 7, d=(w1c >> 15) & 7, Ad=(w1c >> 9) & 7),
            dict(a=(w0c >> 5) & 0xF, c=w0c & 0x1F, Aa=(w1c >> 21) & 7, Ac=(w1c >> 18) & 7,
                 b=(w1c >> 24) & 0xF, Ab=(w1c >> 3) & 7, d=(w1c >> 6) & 7, Ad=w1c & 7),
        ]
        two = ct == G_CYC_2CYCLE
        uses_t0 = uses_t1 = False
        def rgb_in(kind, sel, ch, cycle):
            nonlocal uses_t0, uses_t1
            comb = "cc" + ch if cycle else "0"
            # Second cycle quirk: TEXEL0 reads texel 1, TEXEL1 reads (next pixel's) texel 0.
            t0n, t1n = ("t0", "t1") if cycle == 0 else ("t1", "t0")
            names = {0: comb, 1: t0n + ch, 2: t1n + ch, 3: "P" + ch, 4: "s" + ch, 5: "E" + ch}
            if kind == "a":
                if sel == 6: return "255"
                if sel == 7: return "0"  # noise → 0 (deterministic)
                if sel > 7: return "0"
            elif kind == "b":
                if sel >= 6: return "0"
            elif kind == "c":
                ext = {6: "0", 7: ("cca" if cycle else "0"), 8: t0n + "a", 9: t1n + "a",
                       10: "Pa", 11: "sa", 12: "Ea", 13: "LF", 14: "PLF", 15: "0"}
                if sel >= 16: return "0"
                if sel >= 6: r = ext[sel]
                else: r = names.get(sel, "0")
                uses_t0 |= "t0" in r; uses_t1 |= "t1" in r
                return r
            elif kind == "d":
                if sel == 6: return "255"
                if sel == 7: return "0"
            r = names.get(sel, "0")
            uses_t0 |= "t0" in r; uses_t1 |= "t1" in r
            return r
        def a_in(kind, sel, cycle):
            nonlocal uses_t0, uses_t1
            comb = "cca" if cycle else "0"
            t0n, t1n = ("t0a", "t1a") if cycle == 0 else ("t1a", "t0a")
            if kind == "c":
                m = {0: "LF", 1: t0n, 2: t1n, 3: "Pa", 4: "sa", 5: "Ea", 6: "PLF", 7: "0"}
            else:
                m = {0: comb, 1: t0n, 2: t1n, 3: "Pa", 4: "sa", 5: "Ea", 6: "255", 7: "0"}
            r = m[sel]
            uses_t0 |= "t0" in r; uses_t1 |= "t1" in r
            return r
        lines = []
        def emit_cycle(i):
            cs = cyc[i]
            for ch in "rgb":
                A = rgb_in("a", cs["a"], ch, i); B = rgb_in("b", cs["b"], ch, i)
                C = rgb_in("c", cs["c"], ch, i); D = rgb_in("d", cs["d"], ch, i)
                lines.append(f"n{ch} = (({A}) - ({B})) * ({C}) / 256.0 + ({D})")
            A = a_in("a", cs["Aa"], i); B = a_in("b", cs["Ab"], i); C = a_in("c", cs["Ac"], i); D = a_in("d", cs["Ad"], i)
            lines.append(f"na = (({A}) - ({B})) * ({C}) / 256.0 + ({D})")
            lines.append("ccr = 0 if nr < 0 else (255 if nr > 255 else nr)")
            lines.append("ccg = 0 if ng < 0 else (255 if ng > 255 else ng)")
            lines.append("ccb = 0 if nb < 0 else (255 if nb > 255 else nb)")
            lines.append("cca = 0 if na < 0 else (255 if na > 255 else na)")
        if ct == G_CYC_COPY:
            uses_t0 = True
            lines.append("ccr, ccg, ccb, cca = t0r, t0g, t0b, t0a")
        elif ct == G_CYC_FILL:
            lines.append("ccr = ccg = ccb = cca = 0")
        else:
            emit_cycle(0)
            if two:
                emit_cycle(1)
        z_cmp = bool(oml & RM_Z_CMP) and self.zimg and ct not in (G_CYC_COPY, G_CYC_FILL)
        z_upd = bool(oml & RM_Z_UPD) and self.zimg and ct not in (G_CYC_COPY, G_CYC_FILL)
        zmode = (oml >> 10) & 3
        prim_z_src = bool(oml & 0x4)
        alpha_cmp = (oml & 3) == 1 and ct != G_CYC_FILL
        cvg_sel = bool(oml & RM_ALPHA_CVG_SEL) and ct not in (G_CYC_COPY, G_CYC_FILL)
        force_bl = bool(oml & RM_FORCE_BL)
        # Blender: cycle0 bits 31..18, cycle1 bits 29..16.
        bl = [((oml >> 30) & 3, (oml >> 26) & 3, (oml >> 22) & 3, (oml >> 18) & 3),
              ((oml >> 28) & 3, (oml >> 24) & 3, (oml >> 20) & 3, (oml >> 16) & 3)]
        need_mem = False
        blend_lines = []
        def emit_blend(i, final):
            nonlocal need_mem
            P, A, M, B = bl[i]
            cin = ("ccr", "ccg", "ccb") if i == 0 or not two else ("blr", "blg", "blb")
            pc = {0: cin, 1: ("mr", "mg", "mb"), 2: ("BLr", "BLg", "BLb"), 3: ("FGr", "FGg", "FGb")}
            av = {0: "cca", 1: "FGa", 2: "sa", 3: "0"}[A]
            bv = {0: f"(255 - {av})", 1: "255", 2: "255", 3: "0"}[B]
            if P == 1 or M == 1:
                need_mem = True
            p = pc[P]; mm = pc[M]
            if final and not force_bl:
                blend_lines.append(f"blr, blg, blb = {cin[0]}, {cin[1]}, {cin[2]}")
                return
            blend_lines.append(f"_den = ({av}) + ({bv})")
            blend_lines.append("if _den <= 0: _den = 255")
            for k, ch in enumerate("rgb"):
                blend_lines.append(f"bl{ch} = ({p[k]} * ({av}) + {mm[k]} * ({bv})) / _den")
        if ct in (G_CYC_1CYCLE, G_CYC_2CYCLE):
            if two:
                emit_blend(0, False)
                emit_blend(1, True)
            else:
                emit_blend(0, True)
        else:
            blend_lines.append("blr, blg, blb = ccr, ccg, ccb")
        need_mem = need_mem and (bool(oml & RM_IM_RD) or force_bl)
        src = []
        tparams = ", ".join(f"TX{i}, W{i}, SCS{i}, SCT{i}, SL{i}, TL{i}, MX{i}, MBX{i}, HIX{i}, NX{i}, "
                            f"MY{i}, MBY{i}, HIY{i}, NY{i}" for i in (0, 1))
        src.append("def make(rd, cimg, cstride, zimg, zstride, PZ, Pr, Pg, Pb, Pa, Er, Eg, Eb, Ea, "
                   "BLr, BLg, BLb, BLa, FGr, FGg, FGb, FGa, PLF, " + tparams + "):")
        src.append(" def span(y, x0, x1, z, dz, iw, diw, sw, dsw, tw, dtw, r, dr, g, dg, b, db, a, da):")
        src.append("  rowc = cimg + y * cstride")
        src.append("  rowz = zimg + y * zstride")
        src.append("  n = 0")
        src.append("  for x in range(x0, x1):")
        body = []
        body.append("zc = z; z += dz; ic = iw; iw += diw; sc = sw; sw += dsw; tc = tw; tw += dtw")
        body.append("sr = r; r += dr; sg = g; g += dg; sb = b; b += db; sa = a; a += da")
        if z_cmp or z_upd:
            body.append("zo = rowz + x * 2")
            body.append("zv = PZ if PZS else int(zc)")
            body.append("zv = 0 if zv < 0 else (0x3FFFF if zv > 0x3FFFF else zv)")
        if z_cmp:
            body.append("old = ZD[(rd[zo] << 8) | rd[zo + 1]]")
            if zmode == ZMODE_DEC:
                body.append("if zv > old + 0x400 or zv < old - 0x400: continue")
            elif zmode == ZMODE_XLU:
                body.append("if zv > old: continue")
            else:
                body.append("if zv > old: continue")
        if uses_t0 or uses_t1:
            if persp:
                body.append("_w = 1.0 / ic if ic else 0.0")
                body.append("ss = sc * _w; tt = tc * _w")
            else:
                body.append("ss = sc; tt = tc")
            if tex_modes is None:
                body.append("t0r = t0g = t0b = t0a = t1r = t1g = t1b = t1a = 0")  # probe build only
            else:
                body.extend(_emit_sample("t0", 0, tex_modes[0], bilerp))
                if uses_t1:
                    body.extend(_emit_sample("t1", 1, tex_modes[1], bilerp))
        body.extend(lines)
        if ct == G_CYC_COPY:
            body.append("if t0a == 0 and alpha_copy: continue")
        if alpha_cmp and ct != G_CYC_COPY:
            body.append("if cca < BLa or cca == 0: continue")
        if cvg_sel:
            body.append("if cca < 32: continue")
        co = "rowc + x * %d" % bpp
        if need_mem:
            body.append(f"co = {co}")
            if bpp == 2:
                body.append("mp = (rd[co] << 8) | rd[co + 1]")
                body.append("mr = ((mp >> 11) & 31) << 3; mg = ((mp >> 6) & 31) << 3; mb = ((mp >> 1) & 31) << 3")
            elif bpp == 4:
                body.append("mr = rd[co]; mg = rd[co + 1]; mb = rd[co + 2]")
            else:
                body.append("mr = mg = mb = rd[co]")
        body.extend(blend_lines)
        if not need_mem:
            body.append(f"co = {co}")
        if bpp == 2:
            body.append("ri = int(blr); gi = int(blg); bi = int(blb)")
            body.append("px = ((ri >> 3) << 11) | ((gi >> 3) << 6) | ((bi >> 3) << 1) | 1")
            body.append("rd[co] = px >> 8; rd[co + 1] = px & 255")
        elif bpp == 4:
            body.append("rd[co] = int(blr); rd[co + 1] = int(blg); rd[co + 2] = int(blb); rd[co + 3] = int(cca)")
        else:
            body.append("rd[co] = int(blr)")
        if z_upd:
            body.append("zw = ZE[zv]")
            body.append("rd[zo] = zw >> 8; rd[zo + 1] = zw & 255")
        body.append("n += 1")
        for ln in body:
            src.append("   " + ln)
        src.append("  STATS['pixels'] += n")
        src.append("  return n")
        src.append(" return span")
        code = "\n".join(src)
        env = {"ZD": _Z_DECODE, "ZE": _Z_ENCODE, "PZS": prim_z_src, "LF": 0,
               "alpha_copy": bool(oml & 1), "STATS": self.stats}
        ns: Dict[str, Any] = {}
        exec(compile(code, "<rdp-span>", "exec"), env, ns)
        uses_tex = uses_t0 or uses_t1 or ct == G_CYC_COPY
        make_np = None
        if not rect and _np is not None and (tex_modes is not None or not (uses_t0 or uses_t1)):
            make_np = _build_tri_np(src[0], body, prim_z_src, env)
        return ns["make"], uses_tex, uses_t1, bilerp, bpp, make_np


# ── HLE graphics microcode (Fast3D / F3DEX / F3DLX / F3DEX2) → SoftRDP ──
UCODE_F3D, UCODE_F3DEX, UCODE_F3DEX2, UCODE_S2DEX, UCODE_S2DEX2 = "f3d", "f3dex", "f3dex2", "s2dex", "s2dex2"
def classify_ucode_text(text: str) -> str:
    """Family from a ucode banner, e.g. 'RSP Gfx ucode F3DEX       fifo 2.08 Yoshitaka Yasumoto'.

    F3DEX2 never says "F3DEX2": it is F3DEX/F3DZEX/F3DLX with a 2.x version.
    """
    import re
    if "SW Version: 2.0" in text or "SGI U64 GFX SW TEAM" in text:
        return UCODE_F3D
    m = re.search(r"ucode\s+([A-Z0-9.]+)", text)
    if not m:
        return ""
    name = m.group(1).upper()
    ver = re.search(r"(\d)\.\d+", text[m.end():])
    major = int(ver.group(1)) if ver else 1
    if name.startswith("S2DEX"):
        return UCODE_S2DEX2 if major >= 2 else UCODE_S2DEX
    if name.startswith(("F3D", "L3D")):
        return UCODE_F3DEX2 if major >= 2 else UCODE_F3DEX
    return ""


def detect_gfx_ucode(rdram: bytearray, ucode_data: int, size: int = 0x800) -> Tuple[str, str]:
    """Identify the graphics microcode from the banner text in its data segment."""
    base = ucode_data & 0xFFFFFF
    blob = bytes(rdram[base:base + max(0x100, min(size or 0x800, 0x1000))])
    for marker in (b"RSP Gfx ucode", b"RSP SW Version", b"SGI U64 GFX SW TEAM"):
        i = blob.find(marker)
        if i >= 0:
            j = i
            while j < len(blob) and 0x20 <= blob[j] < 0x7F:
                j += 1
            text = blob[i:j].decode("ascii", "replace")
            fam = classify_ucode_text(text)
            if fam:
                return fam, text
    return "", ""


# Geometry-mode bit layouts per microcode family.
_GM_F3D = dict(zbuffer=0x1, shade=0x4, smooth=0x200, cull_front=0x1000, cull_back=0x2000,
               fog=0x10000, lighting=0x20000, texgen=0x40000, texgen_lin=0x80000)
_GM_F3DEX2 = dict(zbuffer=0x1, shade=0x4, smooth=0x200000, cull_front=0x200, cull_back=0x400,
                  fog=0x10000, lighting=0x20000, texgen=0x40000, texgen_lin=0x80000)


class GfxVertex:
    __slots__ = ("x", "y", "z", "w", "sx", "sy", "sz", "s", "t", "r", "g", "b", "a", "clip")

    def __init__(self):
        self.x = self.y = self.z = 0.0; self.w = 1.0
        self.sx = self.sy = self.sz = 0.0
        self.s = self.t = 0.0
        self.r = self.g = self.b = self.a = 0
        self.clip = 0


def _mat_mul(a, b):
    return [[a[i][0] * b[0][j] + a[i][1] * b[1][j] + a[i][2] * b[2][j] + a[i][3] * b[3][j]
             for j in range(4)] for i in range(4)]


def _mat_ident():
    return [[1.0 if i == j else 0.0 for j in range(4)] for i in range(4)]


class GfxHLE:
    """Interprets an OSTask graphics display list like the RSP microcode would."""

    def __init__(self, core, rdp: SoftRDP):
        self.core = core
        self.rdp = rdp
        self.ucode = UCODE_F3D
        self.reset()

    def reset(self):
        self.segments = [0] * 16
        self.mv_stack: List[List[List[float]]] = []
        self.modelview = _mat_ident()
        self.projection = _mat_ident()
        self.mvp = _mat_ident()
        self.verts = [GfxVertex() for _ in range(80)]
        self.geom = 0
        self.vp_scale = (160.0, 120.0, 511.0); self.vp_trans = (160.0, 120.0, 511.0)
        self.num_lights = 1
        self.lights = [((255, 255, 255), (0.0, 0.0, 1.0)) for _ in range(10)]
        self.lookat = [(0.0, 1.0, 0.0), (1.0, 0.0, 0.0)]
        self.fog_mult = 0; self.fog_ofs = 0
        self.tex_on = False; self.tex_tile = 0; self.tex_level = 0
        self.tex_s = 1.0; self.tex_t = 1.0
        self.half1 = 0; self.half2 = 0
        self.dl_stack: List[int] = []
        self.ended = False

    # ── memory helpers (physical RDRAM, never through the CPU TLB) ──
    def seg(self, addr: int) -> int:
        return ((self.segments[(addr >> 24) & 0xF] + (addr & 0xFFFFFF)) & 0xFFFFFF)

    def r32(self, pa: int) -> int:
        rd = self.core.rdram
        pa &= 0xFFFFFC
        if pa + 4 > len(rd):
            return 0
        return (rd[pa] << 24) | (rd[pa + 1] << 16) | (rd[pa + 2] << 8) | rd[pa + 3]

    def load_mtx(self, addr: int):
        pa = self.seg(addr)
        rd = self.core.rdram
        if pa + 64 > len(rd):
            return _mat_ident()
        hi = struct.unpack_from(">16h", rd, pa)
        lo = struct.unpack_from(">16H", rd, pa + 32)
        return [[hi[i * 4 + j] + lo[i * 4 + j] / 65536.0 for j in range(4)] for i in range(4)]

    def _gm(self):
        return _GM_F3DEX2 if self.ucode in (UCODE_F3DEX2, UCODE_S2DEX2) else _GM_F3D

    # ── entry ──
    def run_task(self, data_ptr: int, ucode: str):
        rdp = self.rdp
        rdp._batching = True
        try:
            return self._run_task(data_ptr, ucode)
        finally:
            rdp._batching = False
            rdp._flush_batch()

    def _run_task(self, data_ptr: int, ucode: str):
        self.ucode = ucode or UCODE_F3D
        self.ended = False
        self.dl_stack = []
        pc = data_ptr & 0xFFFFFF
        steps = 0
        rdp = self.rdp
        is2 = self.ucode in (UCODE_F3DEX2, UCODE_S2DEX2)
        s2d = self.ucode in (UCODE_S2DEX, UCODE_S2DEX2)
        while not self.ended and steps < 1_000_000:
            w0 = self.r32(pc); w1 = self.r32(pc + 4)
            pc += 8
            steps += 1
            op = w0 >> 24
            # RDP passthrough commands are shared by every ucode.
            if op >= 0xE4 and not (is2 and op in (0xE1, 0xE2, 0xE3)):
                pc = self.rdp_cmd(op, w0, w1, pc)
                continue
            if s2d:
                pc = self.op_s2dex(op, w0, w1, pc)
            elif is2:
                pc = self.op_f3dex2(op, w0, w1, pc)
            else:
                pc = self.op_f3d(op, w0, w1, pc)
            if pc is None:
                if not self.dl_stack:
                    break
                pc = self.dl_stack.pop()
        if steps >= 1_000_000:
            self.core.note_unimpl("gfx:runaway-dl")

    def _call(self, pc, w0_param, w1):
        target = self.seg(w1)
        if w0_param == 0:  # G_DL_PUSH
            if len(self.dl_stack) < 32:
                self.dl_stack.append(pc)
        return target

    # ── RDP commands (0xE4..0xFF) ──
    def rdp_cmd(self, op, w0, w1, pc):
        rdp = self.rdp
        if op == 0xFF:
            rdp.set_color_image((w0 >> 21) & 7, (w0 >> 19) & 3, (w0 & 0xFFF) + 1, self.seg(w1))
        elif op == 0xFE:
            rdp.zimg = self.seg(w1)
        elif op == 0xFD:
            rdp.set_texture_image((w0 >> 21) & 7, (w0 >> 19) & 3, (w0 & 0xFFF) + 1, self.seg(w1))
        elif op == 0xFC:
            rdp.combine = (w0 & 0xFFFFFF, w1)
        elif op == 0xFB:
            rdp.env = ((w1 >> 24) & 255, (w1 >> 16) & 255, (w1 >> 8) & 255, w1 & 255)
        elif op == 0xFA:
            rdp.prim = ((w1 >> 24) & 255, (w1 >> 16) & 255, (w1 >> 8) & 255, w1 & 255)
            rdp.prim_lod_frac = w0 & 0xFF
        elif op == 0xF9:
            rdp.blend = ((w1 >> 24) & 255, (w1 >> 16) & 255, (w1 >> 8) & 255, w1 & 255)
        elif op == 0xF8:
            rdp.fog = ((w1 >> 24) & 255, (w1 >> 16) & 255, (w1 >> 8) & 255, w1 & 255)
        elif op == 0xF7:
            rdp.fill_color = w1
        elif op == 0xF6:
            rdp.fill_rect((w1 >> 12) & 0xFFF, w1 & 0xFFF, (w0 >> 12) & 0xFFF, w0 & 0xFFF)
        elif op == 0xF5:
            rdp.set_tile(w0, w1)
        elif op == 0xF4:
            rdp.load_tile(w0, w1)
        elif op == 0xF3:
            rdp.load_block(w0, w1)
        elif op == 0xF2:
            rdp.set_tile_size(w0, w1)
        elif op == 0xF0:
            rdp.load_tlut(w0, w1)
        elif op == 0xEF:
            rdp.omh = w0 & 0xFFFFFF; rdp.oml = w1
        elif op == 0xEE:
            rdp.prim_z = (w1 >> 16) & 0x7FFF
        elif op == 0xED:
            rdp.scissor = (((w0 >> 12) & 0xFFF) >> 2, (w0 & 0xFFF) >> 2, ((w1 >> 12) & 0xFFF) >> 2, (w1 & 0xFFF) >> 2)
        elif op in (0xE4, 0xE5):
            # Texture rectangle: followed by RDPHALF_1 (s,t) and RDPHALF_2 (dsdx,dtdy).
            h1 = self.r32(pc + 4); h2 = self.r32(pc + 12)
            pc += 16
            xh = (w0 >> 12) & 0xFFF; yh = w0 & 0xFFF
            tile = (w1 >> 24) & 7; xl = (w1 >> 12) & 0xFFF; yl = w1 & 0xFFF
            s = struct.unpack(">h", struct.pack(">H", h1 >> 16))[0]
            t = struct.unpack(">h", struct.pack(">H", h1 & 0xFFFF))[0]
            dsdx = struct.unpack(">h", struct.pack(">H", h2 >> 16))[0]
            dtdy = struct.unpack(">h", struct.pack(">H", h2 & 0xFFFF))[0]
            rdp.tex_rect(tile, xl, yl, xh, yh, s, t, dsdx, dtdy, flip=(op == 0xE5))
        elif op == 0xE9:
            pass  # full sync: DP interrupt is raised by the task completion path
        elif op in (0xE6, 0xE7, 0xE8, 0xEA, 0xEB, 0xEC):
            pass  # load/pipe/tile sync, set key colors (ignored), set convert
        else:
            self.core.note_unimpl(f"gfx:rdp:{op:02X}")
        return pc

    # ── Fast3D / F3DEX (1.x) opcodes ──
    def op_f3d(self, op, w0, w1, pc):
        ex = self.ucode in (UCODE_F3DEX, UCODE_S2DEX)
        if op == 0x01:  # G_MTX
            p = (w0 >> 16) & 0xFF
            self.apply_mtx(self.load_mtx(w1), proj=bool(p & 1), load=bool(p & 2), push=bool(p & 4))
        elif op == 0x03:  # G_MOVEMEM
            self.movemem_f3d((w0 >> 16) & 0xFF, w1)
        elif op == 0x04:  # G_VTX
            if ex:
                n = (w0 >> 10) & 0x3F; v0 = ((w0 >> 16) & 0xFF) >> 1
            else:
                n = ((w0 >> 20) & 0xF) + 1; v0 = (w0 >> 16) & 0xF
            self.load_verts(w1, n, v0)
        elif op == 0x06:  # G_DL
            return self._call(pc, (w0 >> 16) & 0xFF, w1)
        elif op == 0xB8:  # G_ENDDL
            return None
        elif op == 0xBF:  # G_TRI1
            div = 2 if ex else 10
            self.tri(((w1 >> 16) & 0xFF) // div, ((w1 >> 8) & 0xFF) // div, (w1 & 0xFF) // div)
        elif op == 0xB1 and ex:  # G_TRI2
            self.tri(((w0 >> 16) & 0xFF) // 2, ((w0 >> 8) & 0xFF) // 2, (w0 & 0xFF) // 2)
            self.tri(((w1 >> 16) & 0xFF) // 2, ((w1 >> 8) & 0xFF) // 2, (w1 & 0xFF) // 2)
        elif op == 0xB5:  # G_QUAD (F3DEX) / G_LINE3D (Fast3D draws nothing useful)
            if ex:
                v = [((w1 >> s) & 0xFF) // 2 for s in (24, 16, 8, 0)]
                self.tri(v[0], v[1], v[2]); self.tri(v[0], v[2], v[3])
        elif op == 0xB6:  # G_CLEARGEOMETRYMODE
            self.geom &= ~w1
        elif op == 0xB7:  # G_SETGEOMETRYMODE
            self.geom |= w1
        elif op == 0xB9:  # G_SETOTHERMODE_L
            sft = (w0 >> 8) & 0xFF; ln = w0 & 0xFF
            mask = ((1 << ln) - 1) << sft
            self.rdp.oml = (self.rdp.oml & ~mask) | (w1 & mask)
        elif op == 0xBA:  # G_SETOTHERMODE_H
            sft = (w0 >> 8) & 0xFF; ln = w0 & 0xFF
            mask = ((1 << ln) - 1) << sft
            self.rdp.omh = (self.rdp.omh & ~mask) | (w1 & mask)
        elif op == 0xBB:  # G_TEXTURE
            self.texture((w0 >> 11) & 7, (w0 >> 8) & 7, w0 & 0xFF, w1)
        elif op == 0xBC:  # G_MOVEWORD
            self.moveword(w0 & 0xFF, (w0 >> 8) & 0xFFFF, w1)
        elif op == 0xBD:  # G_POPMTX
            if self.mv_stack:
                self.modelview = self.mv_stack.pop(); self._update_mvp()
        elif op == 0xBE:  # G_CULLDL (Fast3D indices are ×40, F3DEX ×2)
            div = 2 if ex else 40
            if self.cull_dl((w0 & 0xFFFF) // div, (w1 & 0xFFFF) // div):
                return None
        elif op == 0xB4:  # G_RDPHALF_1
            self.half1 = w1
        elif op == 0xB3:  # G_RDPHALF_2
            self.half2 = w1
        elif op == 0xB0 and ex:  # G_BRANCH_Z
            v = self.verts[min((w0 & 0xFFF) // 2, 79)]
            if (v.sz / 8.0) * 65536.0 <= w1 or v.w <= 0:
                return self.seg(self.half1)
        elif op == 0xB2 and ex:  # G_MODIFYVTX
            self.modify_vtx((w0 >> 16) & 0xFF, (w0 & 0xFFFF) // 2, w1)
        elif op == 0xAF and ex:  # G_LOAD_UCODE
            pass
        elif op in (0x00, 0xC0):
            pass
        else:
            self.core.note_unimpl(f"gfx:{self.ucode}:{op:02X}")
        return pc

    # ── F3DEX2 opcodes ──
    def op_f3dex2(self, op, w0, w1, pc):
        if op == 0x01:  # G_VTX
            n = (w0 >> 12) & 0xFF; v0 = ((w0 >> 1) & 0x7F) - n
            self.load_verts(w1, n, v0)
        elif op == 0x05:  # G_TRI1
            self.tri(((w0 >> 16) & 0xFF) // 2, ((w0 >> 8) & 0xFF) // 2, (w0 & 0xFF) // 2)
        elif op == 0x06:  # G_TRI2
            self.tri(((w0 >> 16) & 0xFF) // 2, ((w0 >> 8) & 0xFF) // 2, (w0 & 0xFF) // 2)
            self.tri(((w1 >> 16) & 0xFF) // 2, ((w1 >> 8) & 0xFF) // 2, (w1 & 0xFF) // 2)
        elif op == 0x07:  # G_QUAD
            a, b, c = ((w0 >> 16) & 0xFF) // 2, ((w0 >> 8) & 0xFF) // 2, (w0 & 0xFF) // 2
            d, e, f = ((w1 >> 16) & 0xFF) // 2, ((w1 >> 8) & 0xFF) // 2, (w1 & 0xFF) // 2
            self.tri(a, b, c); self.tri(d, e, f)
        elif op == 0x02:  # G_MODIFYVTX
            self.modify_vtx((w0 >> 16) & 0xFF, (w0 & 0xFFFF) // 2, w1)
        elif op == 0x03:  # G_CULLDL
            if self.cull_dl((w0 & 0xFFFF) // 2, (w1 & 0xFFFF) // 2):
                return None
        elif op == 0x04:  # G_BRANCH_Z
            v = self.verts[min((w0 & 0xFFF) // 2, 79)]
            if (v.sz / 8.0) * 65536.0 <= w1 or v.w <= 0:
                return self.seg(self.half1)
        elif op == 0xD7:  # G_TEXTURE
            self.texture((w0 >> 11) & 7, (w0 >> 8) & 7, (w0 >> 1) & 0x7F, w1)
        elif op == 0xD9:  # G_GEOMETRYMODE
            self.geom = (self.geom & (w0 & 0xFFFFFF)) | w1
        elif op == 0xDA:  # G_MTX
            p = (w0 & 0xFF) ^ 0x01
            self.apply_mtx(self.load_mtx(w1), proj=bool(p & 4), load=bool(p & 2), push=bool(p & 1))
        elif op == 0xD8:  # G_POPMTX
            for _ in range(max(1, w1 // 64)):
                if self.mv_stack:
                    self.modelview = self.mv_stack.pop()
            self._update_mvp()
        elif op == 0xDB:  # G_MOVEWORD
            self.moveword((w0 >> 16) & 0xFF, w0 & 0xFFFF, w1)
        elif op == 0xDC:  # G_MOVEMEM
            self.movemem_f3dex2(w0 & 0xFF, ((w0 >> 8) & 0xFF) * 8, w1)
        elif op == 0xDE:  # G_DL
            return self._call(pc, (w0 >> 16) & 0xFF, w1)
        elif op == 0xDF:  # G_ENDDL
            return None
        elif op == 0xE1:  # G_RDPHALF_1
            self.half1 = w1
        elif op == 0xF1:  # G_RDPHALF_2
            self.half2 = w1
        elif op == 0xE2:  # G_SETOTHERMODE_L
            ln = (w0 & 0xFF) + 1; sft = 32 - ((w0 >> 8) & 0xFF) - ln
            mask = ((1 << ln) - 1) << sft
            self.rdp.oml = (self.rdp.oml & ~mask) | (w1 & mask)
        elif op == 0xE3:  # G_SETOTHERMODE_H
            ln = (w0 & 0xFF) + 1; sft = 32 - ((w0 >> 8) & 0xFF) - ln
            mask = ((1 << ln) - 1) << sft
            self.rdp.omh = (self.rdp.omh & ~mask) | (w1 & mask)
        elif op in (0x00, 0xD3, 0xD4, 0xD5, 0xD6, 0xDD, 0xE0):
            pass  # noop / special / dma_io / load_ucode
        else:
            self.core.note_unimpl(f"gfx:{self.ucode}:{op:02X}")
        return pc

    # ── S2DEX / S2DEX2 (2D sprite & background microcode) ──
    # Opcode numbering differs: S2DEX 1.x follows F3DEX, S2DEX2 follows F3DEX2.
    _S2D1 = {0x01: "BG_1CYC", 0x02: "BG_COPY", 0x03: "OBJ_RECTANGLE", 0x04: "OBJ_SPRITE", 0x05: "OBJ_MOVEMEM",
             0xB0: "SELECT_DL", 0xB1: "OBJ_RENDERMODE", 0xB2: "OBJ_RECTANGLE_R", 0xC1: "OBJ_LOADTXTR",
             0xC2: "OBJ_LDTX_SPRITE", 0xC3: "OBJ_LDTX_RECT", 0xC4: "OBJ_LDTX_RECT_R"}
    _S2D2 = {0x01: "OBJ_RECTANGLE", 0x02: "OBJ_SPRITE", 0x04: "SELECT_DL", 0x05: "OBJ_LOADTXTR",
             0x06: "OBJ_LDTX_SPRITE", 0x07: "OBJ_LDTX_RECT", 0x08: "OBJ_LDTX_RECT_R", 0x09: "BG_1CYC",
             0x0A: "BG_COPY", 0x0B: "OBJ_RENDERMODE", 0xDA: "OBJ_RECTANGLE_R", 0xDC: "OBJ_MOVEMEM"}

    def op_s2dex(self, op, w0, w1, pc):
        table = self._S2D2 if self.ucode == UCODE_S2DEX2 else self._S2D1
        name = table.get(op)
        if name is None:
            # Shared GBI ops (DL, ENDDL, othermode, moveword...) follow the base family's numbering.
            if self.ucode == UCODE_S2DEX2:
                return self.op_f3dex2(op, w0, w1, pc)
            return self.op_f3d(op, w0, w1, pc)
        a = self.seg(w1)
        if name in ("BG_1CYC", "BG_COPY"):
            self.s2d_bg(a, scaled=(name == "BG_1CYC"))
        elif name == "OBJ_RECTANGLE":
            self.s2d_obj_rect(a, rotate=False)
        elif name == "OBJ_RECTANGLE_R":
            self.s2d_obj_rect(a, rotate=True)
        elif name == "OBJ_SPRITE":
            self.s2d_obj_sprite(a)
        elif name == "OBJ_LOADTXTR":
            self.s2d_load_txtr(a)
        elif name == "OBJ_LDTX_SPRITE":
            self.s2d_load_txtr(a); self.s2d_obj_sprite(a + 24)
        elif name == "OBJ_LDTX_RECT":
            self.s2d_load_txtr(a); self.s2d_obj_rect(a + 24, rotate=False)
        elif name == "OBJ_LDTX_RECT_R":
            self.s2d_load_txtr(a); self.s2d_obj_rect(a + 24, rotate=True)
        elif name == "OBJ_MOVEMEM":
            self.s2d_movemem(w0, a)
        elif name == "OBJ_RENDERMODE":
            self.obj_rendermode = w1
        elif name == "SELECT_DL":
            self.core.note_unimpl("gfx:s2dex:SELECT_DL")
        return pc

    def _rd16s(self, pa):
        v = (self.core.rdram[pa] << 8) | self.core.rdram[pa + 1]
        return v - 0x10000 if v & 0x8000 else v

    def _rd16(self, pa):
        return (self.core.rdram[pa] << 8) | self.core.rdram[pa + 1]

    def s2d_movemem(self, w0, pa):
        """uObjMtx (A,B,C,D s15.16; X,Y s10.2; BaseScaleX/Y u5.10) or uObjSubMtx (X,Y,BaseScale)."""
        size = (w0 & 0xFFFF) if self.ucode != UCODE_S2DEX2 else (((w0 >> 19) & 0x1F) + 1) * 8
        if size >= 0x18 or (w0 & 0xFF) == 0x17:
            a, b, c, d = struct.unpack_from(">iiii", self.core.rdram, pa)
            x, y, bsx, bsy = struct.unpack_from(">hhHH", self.core.rdram, pa + 16)
            self.obj_mtx = [a / 65536.0, b / 65536.0, c / 65536.0, d / 65536.0, x / 4.0, y / 4.0,
                            bsx / 1024.0, bsy / 1024.0]
        else:
            x, y, bsx, bsy = struct.unpack_from(">hhHH", self.core.rdram, pa)
            m = list(getattr(self, "obj_mtx", [1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 1.0, 1.0]))
            m[4], m[5], m[6], m[7] = x / 4.0, y / 4.0, bsx / 1024.0, bsy / 1024.0
            self.obj_mtx = m

    def s2d_load_txtr(self, pa):
        """uObjTxtr: TXTRBLOCK (LoadBlock), TXTRTILE (LoadTile) or TLUT."""
        rd = self.core.rdram
        typ = struct.unpack_from(">I", rd, pa)[0]
        image = struct.unpack_from(">I", rd, pa + 4)[0]
        img = self.seg(image)
        f1, f2, f3 = struct.unpack_from(">HHH", rd, pa + 8)
        rdp = self.rdp
        if typ == 0x00001033:      # G_OBJLT_TXTRBLOCK: tmem, tsize (words-1), tline (dxt)
            tmem, tsize, tline = f1, f2, f3
            rdp.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, 1, img)
            rdp.set_tile((G_IM_SIZ_16b << 19) | (tmem & 0x1FF), 7 << 24)
            texels = (tsize + 1) * 4
            rdp.load_block(0, (7 << 24) | ((texels - 1) << 12) | (tline & 0xFFF))
        elif typ == 0x00FC1034:    # G_OBJLT_TXTRTILE: tmem, twidth (16b texels-1), theight ((rows<<2)-1)
            tmem, twidth, theight = f1, f2, f3
            width16 = twidth + 1
            rows = (theight + 1) >> 2
            rdp.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, width16, img)
            rdp.set_tile((G_IM_SIZ_16b << 19) | (((width16 + 3) >> 2) << 9) | (tmem & 0x1FF), 7 << 24)
            rdp.load_tile(0, (7 << 24) | (((width16 - 1) << 2) << 12) | ((rows - 1) << 2))
        elif typ == 0x00000030:    # G_OBJLT_TLUT: phead (256+index), pnum (count-1)
            phead, pnum = f1, f2
            rdp.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, 1, img)
            rdp.set_tile((phead & 0x1FF), 7 << 24)
            rdp.load_tlut(0, (7 << 24) | ((pnum << 2) << 12))
        else:
            self.core.note_unimpl(f"gfx:s2dex:txtr:{typ:08X}")

    def _s2d_sprite(self, pa):
        rd = self.core.rdram
        objX, scaleW, imageW, _px, objY, scaleH, imageH, _py, stride, adrs = struct.unpack_from(">hHHHhHHHHH", rd, pa)
        fmt, siz, pal, flags = rd[pa + 20], rd[pa + 21], rd[pa + 22], rd[pa + 23]
        return objX, scaleW or 1024, imageW, objY, scaleH or 1024, imageH, stride, adrs, fmt, siz, pal, flags

    def _s2d_tile(self, stride, adrs, fmt, siz, pal, w_texels, h_texels):
        rdp = self.rdp
        rdp.set_tile((fmt << 21) | (siz << 19) | ((stride & 0x1FF) << 9) | (adrs & 0x1FF), (0 << 24) | (pal << 20))
        rdp.set_tile_size(0, (((w_texels - 1) << 2) << 12) | ((h_texels - 1) << 2))

    def s2d_obj_rect(self, pa, rotate: bool):
        """OBJ_RECTANGLE(_R): axis-aligned sprite from TMEM, scaled by scaleW/H (u5.10 = 1/zoom)."""
        objX, scaleW, imageW, objY, scaleH, imageH, stride, adrs, fmt, siz, pal, flags = self._s2d_sprite(pa)
        tw = max(1, imageW >> 5); th = max(1, imageH >> 5)
        self._s2d_tile(stride, adrs, fmt, siz, pal, tw, th)
        x0 = objX / 4.0; y0 = objY / 4.0
        if rotate and hasattr(self, "obj_mtx"):
            m = self.obj_mtx
            x0 = m[4] + objX / 4.0 / m[6]; y0 = m[5] + objY / 4.0 / m[7]
            scaleW = int(scaleW * m[6]) or 1; scaleH = int(scaleH * m[7]) or 1
        w = tw * 1024.0 / scaleW; h = th * 1024.0 / scaleH
        s0 = (tw - 1) * 32 if flags & 0x01 else 0       # G_OBJ_FLAG_FLIPS
        t0 = (th - 1) * 32 if flags & 0x10 else 0       # G_OBJ_FLAG_FLIPT
        dsdx = -scaleW if flags & 0x01 else scaleW
        dtdy = -scaleH if flags & 0x10 else scaleH
        self._s2d_rect(x0, y0, x0 + w, y0 + h, s0, t0, dsdx, dtdy)

    def _s2d_rect(self, x0, y0, x1, y1, s, t, dsdx, dtdy):
        """Texture rectangle in screen pixels [x0,x1)×[y0,y1); handles copy-mode conventions."""
        copy = self.rdp.cycle_type in (G_CYC_COPY, G_CYC_FILL)
        xh = int(x1 * 4) - (4 if copy else 0); yh = int(y1 * 4) - (4 if copy else 0)
        self.rdp.tex_rect(0, int(x0 * 4), int(y0 * 4), xh, yh, int(s), int(t),
                          int(dsdx * 4) if self.rdp.cycle_type == G_CYC_COPY else int(dsdx), int(dtdy))

    def s2d_obj_sprite(self, pa):
        """OBJ_SPRITE: sprite transformed by the 2D object matrix (rotation/scale) as two triangles."""
        objX, scaleW, imageW, objY, scaleH, imageH, stride, adrs, fmt, siz, pal, flags = self._s2d_sprite(pa)
        tw = max(1, imageW >> 5); th = max(1, imageH >> 5)
        self._s2d_tile(stride, adrs, fmt, siz, pal, tw, th)
        m = getattr(self, "obj_mtx", [1.0, 0.0, 0.0, 1.0, 0.0, 0.0, 1.0, 1.0])
        lx0 = objX / 4.0; ly0 = objY / 4.0
        lx1 = lx0 + tw * 1024.0 / scaleW; ly1 = ly0 + th * 1024.0 / scaleH
        def xf(x, y):
            return (m[0] * x + m[1] * y + m[4], m[2] * x + m[3] * y + m[5])
        s_a, s_b = (tw, 0) if flags & 0x01 else (0, tw)
        t_a, t_b = (th, 0) if flags & 0x10 else (0, th)
        corners = [(lx0, ly0, s_a, t_a), (lx1, ly0, s_b, t_a), (lx1, ly1, s_b, t_b), (lx0, ly1, s_a, t_b)]
        z = float(self.rdp.prim_z << 3)
        v = []
        for x, y, s_, t_ in corners:
            sx, sy = xf(x, y)
            v.append((sx, sy, z, 1.0, float(s_), float(t_), 255.0, 255.0, 255.0, 255.0))
        self.rdp.draw_triangle(v[0], v[1], v[2], 0, True)
        self.rdp.draw_triangle(v[0], v[2], v[3], 0, True)

    def s2d_bg(self, pa, scaled: bool):
        """BG_COPY / BG_1CYC: stream the DRAM image through TMEM in strips and draw texrects.

        uObjBg: imageX(u10.5) imageW(u10.2) frameX(s10.2) frameW(u10.2) imageY imageH frameY frameH
                imagePtr imageLoad imageFmt imageSiz imagePal imageFlip [scaleW scaleH imageYorig]
        """
        rd = self.core.rdram
        imageX, imageW, frameX, frameW, imageY, imageH, frameY, frameH = struct.unpack_from(">HHhHHHhH", rd, pa)
        ptr = self.seg(struct.unpack_from(">I", rd, pa + 16)[0])
        _load, fmt, siz, pal, flip = struct.unpack_from(">HBBHH", rd, pa + 20)
        scaleW = scaleH = 1024
        if scaled:
            scaleW, scaleH = struct.unpack_from(">HH", rd, pa + 28)
            scaleW = scaleW or 1024; scaleH = scaleH or 1024
        iw = max(1, imageW >> 2); ih = max(1, imageH >> 2)
        fx0 = frameX / 4.0; fy0 = frameY / 4.0
        fw = frameW / 4.0; fh = frameH / 4.0
        if fw <= 0 or fh <= 0:
            return
        row_bytes = (iw << siz) >> 1
        row_words = (row_bytes + 7) >> 3
        cap = 0x800 if fmt == G_IM_FMT_CI else 0x1000
        strip = max(1, min(ih, cap // max(8, row_words * 8)))
        rdp = self.rdp
        step_y = scaleH / 1024.0
        step_x = scaleW / 1024.0
        sx0 = imageX / 32.0
        img_y = imageY / 32.0
        sy = fy0
        y_end = fy0 + fh
        while sy < y_end - 1e-6:
            # Image row for this screen row (wrapping vertically around the image).
            iy = int(img_y) % ih
            rows = min(strip, ih - iy)
            span_h = rows / step_y
            yb = min(y_end, sy + span_h)
            rdp.set_texture_image(fmt, siz, iw, ptr + iy * row_bytes)
            rdp.set_tile((fmt << 21) | (siz << 19) | ((row_words & 0x1FF) << 9), (7 << 24) | (pal << 20))
            rdp.load_tile(0, (7 << 24) | (((iw - 1) << 2) << 12) | ((rows - 1) << 2))
            rdp.set_tile((fmt << 21) | (siz << 19) | ((row_words & 0x1FF) << 9), (0 << 24) | (pal << 20))
            rdp.set_tile_size(0, (((iw - 1) << 2) << 12) | ((rows - 1) << 2))
            # Horizontal wrap: up to two rects per strip.
            x = fx0; s = sx0 % iw
            while x < fx0 + fw - 1e-6:
                seg_w = min(fx0 + fw - x, (iw - s) / step_x)
                frac_t = (img_y - int(img_y)) * 32
                self._s2d_rect(x, sy, x + seg_w, yb, s * 32, frac_t, scaleW, scaleH)
                x += seg_w; s = 0.0
            img_y += (yb - sy) * step_y
            sy = yb

    # ── shared state ops ──
    def _update_mvp(self):
        self.mvp = _mat_mul(self.modelview, self.projection)

    def apply_mtx(self, m, proj: bool, load: bool, push: bool):
        if proj:
            self.projection = m if load else _mat_mul(m, self.projection)
        else:
            if push and len(self.mv_stack) < 32:
                self.mv_stack.append(self.modelview)
            self.modelview = m if load else _mat_mul(m, self.modelview)
        self._update_mvp()

    def texture(self, level, tile, on, w1):
        self.tex_level = level; self.tex_tile = tile; self.tex_on = bool(on)
        ss = (w1 >> 16) & 0xFFFF; st = w1 & 0xFFFF
        self.tex_s = (ss + (1 if ss == 0xFFFF else 0)) / 65536.0 if ss else 1.0
        self.tex_t = (st + (1 if st == 0xFFFF else 0)) / 65536.0 if st else 1.0

    def moveword(self, index, offset, w1):
        if index == 6:  # G_MW_SEGMENT
            self.segments[(offset >> 2) & 0xF] = w1 & 0xFFFFFF
        elif index == 2:  # G_MW_NUMLIGHT
            if self.ucode == UCODE_F3DEX2:
                self.num_lights = max(0, min(7, w1 // 24))
            else:
                self.num_lights = max(0, min(7, ((w1 - 0x80000000) & 0xFFFFFFFF) // 32 - 1))
        elif index == 8:  # G_MW_FOG
            self.fog_mult = struct.unpack(">h", struct.pack(">H", w1 >> 16))[0]
            self.fog_ofs = struct.unpack(">h", struct.pack(">H", w1 & 0xFFFF))[0]
        elif index == 10:  # G_MW_LIGHTCOL
            n = offset // (24 if self.ucode == UCODE_F3DEX2 else 32)
            if 0 <= n < 10:
                col, d = self.lights[n]
                self.lights[n] = (((w1 >> 24) & 255, (w1 >> 16) & 255, (w1 >> 8) & 255), d)
        elif index in (0, 4, 12, 14):
            pass  # force matrix (rare), clip ratio, points/modify, perspnorm

    def _read_light(self, pa):
        rd = self.core.rdram
        if pa + 16 > len(rd):
            return (0, 0, 0), (0.0, 0.0, 1.0)
        col = (rd[pa], rd[pa + 1], rd[pa + 2])
        dx, dy, dz = struct.unpack_from(">bbb", rd, pa + 8)
        n = math.sqrt(dx * dx + dy * dy + dz * dz) or 1.0
        return col, (dx / n, dy / n, dz / n)

    def _load_viewport(self, pa):
        rd = self.core.rdram
        if pa + 16 > len(rd):
            return
        v = struct.unpack_from(">8h", rd, pa)
        self.vp_scale = (v[0] / 4.0, v[1] / 4.0, v[2] / 4.0 * 4)
        self.vp_trans = (v[4] / 4.0, v[5] / 4.0, v[6] / 4.0 * 4)

    def movemem_f3d(self, index, w1):
        pa = self.seg(w1)
        if index == 0x80:
            self._load_viewport(pa)
        elif 0x86 <= index <= 0x94:
            self.lights[(index - 0x86) // 2] = self._read_light(pa)
        elif index in (0x82, 0x84):
            col, d = self._read_light(pa)
            self.lookat[0 if index == 0x82 else 1] = d

    def movemem_f3dex2(self, index, offset, w1):
        pa = self.seg(w1)
        if index == 8:  # G_MV_VIEWPORT
            self._load_viewport(pa)
        elif index == 10:  # G_MV_LIGHT: offset 0/24 = lookat, then lights at 24*(n+2)
            n = offset // 24 - 2
            if n >= 0:
                if n < 10:
                    self.lights[n] = self._read_light(pa)
            else:
                # F3DEX2: offset 0 = LookAt X, 24 = LookAt Y (stored as lookat[1] / lookat[0]).
                self.lookat[1 - offset // 24] = self._read_light(pa)[1]
        elif index == 14:  # G_MV_MATRIX (force)
            self.mvp = self.load_mtx(w1)

    # ── vertices ──
    def load_verts(self, addr, n, v0):
        pa = self.seg(addr)
        rd = self.core.rdram
        gm = self._gm()
        lighting = bool(self.geom & gm["lighting"])
        texgen = bool(self.geom & gm["texgen"])
        fog = bool(self.geom & gm["fog"])
        m = self.mvp
        mv = self.modelview
        vs = self.vp_scale; vt = self.vp_trans
        ts, tt = self.tex_s, self.tex_t
        for i in range(max(0, n)):
            dst = v0 + i
            if not (0 <= dst < 80):
                break
            off = pa + i * 16
            if off + 16 > len(rd):
                break
            x, y, z, _f, s, t = struct.unpack_from(">hhhhhh", rd, off)
            c0, c1, c2, a = rd[off + 12], rd[off + 13], rd[off + 14], rd[off + 15]
            v = self.verts[dst]
            cx = x * m[0][0] + y * m[1][0] + z * m[2][0] + m[3][0]
            cy = x * m[0][1] + y * m[1][1] + z * m[2][1] + m[3][1]
            cz = x * m[0][2] + y * m[1][2] + z * m[2][2] + m[3][2]
            cw = x * m[0][3] + y * m[1][3] + z * m[2][3] + m[3][3]
            v.x, v.y, v.z, v.w = cx, cy, cz, cw
            clip = 0
            if cx < -cw: clip |= 1
            if cx > cw: clip |= 2
            if cy < -cw: clip |= 4
            if cy > cw: clip |= 8
            if cz < -cw: clip |= 16  # near
            if cw <= 0: clip |= 32
            v.clip = clip
            iw = 1.0 / cw if abs(cw) > 1e-9 else 1e9
            v.sx = vt[0] + cx * iw * vs[0]
            v.sy = vt[1] - cy * iw * vs[1]
            v.sz = (vt[2] + cz * iw * vs[2]) * 256.0
            if lighting:
                nx = (c0 - 256 if c0 > 127 else c0); ny = (c1 - 256 if c1 > 127 else c1); nz = (c2 - 256 if c2 > 127 else c2)
                tx = nx * mv[0][0] + ny * mv[1][0] + nz * mv[2][0]
                ty = nx * mv[0][1] + ny * mv[1][1] + nz * mv[2][1]
                tz = nx * mv[0][2] + ny * mv[1][2] + nz * mv[2][2]
                ln = math.sqrt(tx * tx + ty * ty + tz * tz) or 1.0
                tx /= ln; ty /= ln; tz /= ln
                nl = self.num_lights
                amb = self.lights[nl][0]
                r, g, b = float(amb[0]), float(amb[1]), float(amb[2])
                for li in range(nl):
                    col, d = self.lights[li]
                    dot = tx * d[0] + ty * d[1] + tz * d[2]
                    if dot > 0:
                        r += col[0] * dot; g += col[1] * dot; b += col[2] * dot
                v.r = 255 if r > 255 else int(r); v.g = 255 if g > 255 else int(g); v.b = 255 if b > 255 else int(b)
                if texgen:
                    lx, ly = self.lookat[1], self.lookat[0]
                    gx = tx * lx[0] + ty * lx[1] + tz * lx[2]
                    gy = tx * ly[0] + ty * ly[1] + tz * ly[2]
                    # Spherical map: [-1,1] → texture space scaled by G_TEXTURE (s10.5 units).
                    s = gx * 512.0 + 512.0
                    t = gy * 512.0 + 512.0
            else:
                v.r, v.g, v.b = c0, c1, c2
            v.a = a
            if fog:
                f = (cz * iw) * self.fog_mult + self.fog_ofs
                v.a = 0 if f < 0 else (255 if f > 255 else int(f))
            v.s = s * ts / 32.0
            v.t = t * tt / 32.0

    def modify_vtx(self, where, vi, val):
        if not (0 <= vi < 80):
            return
        v = self.verts[vi]
        if where == 0x10:  # RGBA
            v.r, v.g, v.b, v.a = (val >> 24) & 255, (val >> 16) & 255, (val >> 8) & 255, val & 255
        elif where == 0x14:  # ST
            s = struct.unpack(">h", struct.pack(">H", val >> 16))[0]
            t = struct.unpack(">h", struct.pack(">H", val & 0xFFFF))[0]
            v.s = s / 32.0; v.t = t / 32.0
        elif where == 0x18:  # XYSCREEN
            v.sx = struct.unpack(">h", struct.pack(">H", val >> 16))[0] / 4.0
            v.sy = struct.unpack(">h", struct.pack(">H", val & 0xFFFF))[0] / 4.0
        elif where == 0x1C:  # ZSCREEN
            v.sz = float(val >> 16) * 8.0

    def cull_dl(self, a, b) -> bool:
        """True when every vertex in [a, b] is outside the same frustum plane."""
        a = max(0, min(79, a)); b = max(0, min(79, b))
        acc = 0x3F
        for i in range(a, b + 1):
            acc &= self.verts[i].clip
            if not acc:
                return False
        return bool(acc & 0xF)

    # ── triangles ──
    def tri(self, i0, i1, i2):
        if self.rdp.fs_skip or max(i0, i1, i2) >= 80:
            return  # frame-skip: projection/clipping only feed the rasterizer
        v0, v1, v2 = self.verts[i0], self.verts[i1], self.verts[i2]
        if v0.clip & v1.clip & v2.clip & 0x0F:
            return  # trivially off-screen
        gm = self._gm()
        poly = [v0, v1, v2]
        if (v0.clip | v1.clip | v2.clip) & 0x30:
            poly = self._clip_near(poly)
            if len(poly) < 3:
                return
            pts = [self._project(v) for v in poly]
        else:
            pts = [(v.sx, v.sy, v.sz, v.w, v) for v in poly]
        # Back/front-face culling in screen space (N64: y down, CCW front).
        ax, ay = pts[0][0], pts[0][1]
        area = (pts[1][0] - ax) * (pts[2][1] - ay) - (pts[2][0] - ax) * (pts[1][1] - ay)
        cull = self.geom & (gm["cull_front"] | gm["cull_back"])
        if cull:
            if (cull & gm["cull_back"]) and area > 0:
                return
            if (cull & gm["cull_front"]) and area < 0:
                return
            if area == 0:
                return
        textured = self.tex_on
        persp = bool(self.rdp.omh & (1 << 19))
        shade = bool(self.geom & gm["shade"])
        smooth = bool(self.geom & gm["smooth"])
        out = []
        for sx, sy, sz, w, v in pts:
            q = (1.0 / w) if (persp and w > 1e-9) else 1.0
            r, g, b, a = (v.r, v.g, v.b, v.a) if shade else (0, 0, 0, v.a)
            out.append((sx, sy, sz, q, v.s * q, v.t * q, float(r), float(g), float(b), float(a)))
        for k in range(1, len(out) - 1):
            self.rdp.draw_triangle(out[0], out[k], out[k + 1], self.tex_tile, textured, smooth)

    def _project(self, v):
        vs = self.vp_scale; vt = self.vp_trans
        iw = 1.0 / v.w if abs(v.w) > 1e-9 else 1e9
        return (vt[0] + v.x * iw * vs[0], vt[1] - v.y * iw * vs[1], (vt[2] + v.z * iw * vs[2]) * 256.0, v.w, v)

    def _clip_near(self, poly):
        """Sutherland–Hodgman against the near plane (z >= -w) in clip space."""
        def inside(v): return v.z >= -v.w and v.w > 1e-5
        out = []
        n = len(poly)
        for i in range(n):
            a = poly[i]; b = poly[(i + 1) % n]
            ia, ib = inside(a), inside(b)
            if ia:
                out.append(a)
            if ia != ib:
                da = a.z + a.w; db = b.z + b.w
                t = da / (da - db) if da != db else 0.0
                nv = GfxVertex()
                for f in ("x", "y", "z", "w", "s", "t"):
                    setattr(nv, f, getattr(a, f) + (getattr(b, f) - getattr(a, f)) * t)
                for f in ("r", "g", "b", "a"):
                    setattr(nv, f, int(getattr(a, f) + (getattr(b, f) - getattr(a, f)) * t))
                if nv.w < 1e-5:
                    nv.w = 1e-5
                out.append(nv)
        return out


# ── HLE audio microcode (ABI1: aspMain / SM64-era Nintendo audio) ──
def _clamp16(v: int) -> int:
    return -32768 if v < -32768 else (32767 if v > 32767 else v)


def _s16(v: int) -> int:
    v &= 0xFFFF
    return v - 0x10000 if v & 0x8000 else v


def _s32(v: int) -> int:
    v &= MASK_32
    return v - 0x100000000 if v & 0x80000000 else v


def _build_resample_lut() -> List[int]:
    """64-phase × 4-tap resampler. Rows are a normalized Gaussian (σ≈0.49) around tap 1+phase.

    Fitted to the shape of the RSP's table (phase 0 ≈ 0.096 / 0.802 / 0.104 / -0.001); audibly
    equivalent but not bit-exact with the real ROM table.
    """
    out = []
    sigma2 = 2 * 0.4895 ** 2
    for ph in range(64):
        p = ph / 64.0
        w = [math.exp(-((k - 1 - p) ** 2) / sigma2) for k in range(4)]
        tot = sum(w)
        out.extend(int(round(x / tot * 32768.0)) for x in w)
    return out


RESAMPLE_LUT = _build_resample_lut()
A_INIT, A_LOOP, A_LEFT, A_VOL, A_AUX = 0x01, 0x02, 0x02, 0x04, 0x08
# Audio microcodes (CRC32 of the first ≤4 KB of ucode text) verified bit-exact against the
# LLE RSP with --verify-audio. Anything else runs on the real microcode (LLE) for safety.
AUDIO_HLE_VERIFIED = {
    0x49158204: "abi1",   # Super Mario 64 (USA): 12 frames, max |diff| 0
}
ABI1_DMEM_BASE = 0x5C0


class AudioHLE:
    """Runs an audio command list against a 4 KB scratch buffer, reading/writing RDRAM."""

    def __init__(self, core):
        self.core = core
        self.buf = bytearray(0x1000)
        self.reset()

    def use_rom_tables(self, rom: bytes):
        """Use the game's own resample table (shipped in its audio ucode data) when present."""
        i = bytes(rom).find(struct.pack(">4h", 0x0C39, 0x66AD, 0x0D46, -0x21))
        if i >= 0 and i + 512 <= len(rom):
            self.lut = list(struct.unpack_from(">256h", rom, i))
        else:
            self.lut = RESAMPLE_LUT

    def reset(self):
        if not hasattr(self, "lut"):
            self.lut = RESAMPLE_LUT
        self.segments = [0] * 64
        self.in_ = self.out = self.count = 0
        self.dry_right = self.wet_left = self.wet_right = 0
        self.vol = [0, 0]; self.target = [0, 0]; self.rate = [0, 0]
        self.dry = self.wet = 0
        self.table = [0] * 128
        self.loop = 0
        self.tasks = 0
        self.saved: Optional[List[Tuple[int, int]]] = None   # SAVEBUFF regions (verification)

    # ── memory helpers ──
    def addr(self, so: int) -> int:
        return (self.segments[(so >> 24) & 0x3F] + (so & 0xFFFFFF)) & 0xFFFFFF

    def rs16(self, o: int) -> int:
        b = self.buf; o &= 0xFFE
        v = (b[o] << 8) | b[o + 1]
        return v - 0x10000 if v & 0x8000 else v

    def ws16(self, o: int, v: int):
        o &= 0xFFE
        v &= 0xFFFF
        self.buf[o] = v >> 8; self.buf[o + 1] = v & 0xFF

    # numpy views of DMEM samples (fast paths only use them when no access wraps 0x1000)
    def _np_r16(self, off: int, n: int):
        return _np.frombuffer(self.buf, dtype=">i2", count=n, offset=off).astype(_np.int64)

    def _np_w16(self, off: int, arr):
        self.buf[off:off + 2 * len(arr)] = _np.clip(arr, -32768, 32767).astype(">i2").tobytes()

    @staticmethod
    def _disjoint(*ranges) -> bool:
        """True if every (start, end) byte range is inside DMEM and no two overlap."""
        rs = sorted(ranges)
        if rs[0][0] < 0 or rs[-1][1] > 0x1000 or any(e > 0x1000 for _s, e in rs):
            return False
        return all(rs[i][1] <= rs[i + 1][0] for i in range(len(rs) - 1))

    def _dram_s16(self, a: int) -> int:
        rd = self.core.rdram; a &= 0xFFFFFE
        v = (rd[a] << 8) | rd[a + 1]
        return v - 0x10000 if v & 0x8000 else v

    def _dram_w16(self, a: int, v: int):
        rd = self.core.rdram; a &= 0xFFFFFE
        v &= 0xFFFF
        rd[a] = v >> 8; rd[a + 1] = v & 0xFF

    # ── command list ──
    def run_abi1(self, alist: int, size: int):
        self.tasks += 1
        rd = self.core.rdram
        a = alist & 0xFFFFF8
        end = a + (size & 0xFFFFF8)
        table = self._ABI1
        while a + 8 <= end and a + 8 <= len(rd):
            w1 = (rd[a] << 24) | (rd[a + 1] << 16) | (rd[a + 2] << 8) | rd[a + 3]
            w2 = (rd[a + 4] << 24) | (rd[a + 5] << 16) | (rd[a + 6] << 8) | rd[a + 7]
            a += 8
            op = (w1 >> 24) & 0x7F
            if op < 16:
                table[op](self, w1, w2)
            else:
                self.core.note_unimpl(f"audio:abi1:{op:02X}")

    # ABI1 commands (w1 = command word, w2 = argument word)
    def _noop(self, w1, w2):
        pass

    def _adpcm(self, w1, w2):
        flags = (w1 >> 16) & 0xFF
        self.adpcm(bool(flags & A_INIT), bool(flags & A_LOOP), self.out, self.in_,
                   (self.count + 31) & ~31, self.addr(w2))

    def _clearbuff(self, w1, w2):
        dmem = (w1 + ABI1_DMEM_BASE) & 0xFFFF
        cnt = w2 & 0xFFF
        if cnt:
            cnt = (cnt + 15) & ~15
            s = dmem & 0xFFF
            self.buf[s:s + cnt] = bytes(min(cnt, 0x1000 - s))

    def _envmixer(self, w1, w2):
        flags = (w1 >> 16) & 0xFF
        self.envmix_exp(bool(flags & A_INIT), bool(flags & A_AUX), self.addr(w2))

    def _loadbuff(self, w1, w2):
        if self.count:
            n = (self.count + 15) & ~15
            src = self.addr(w2) & ~7
            d = self.in_ & 0xFFF
            n = min(n, 0x1000 - d)
            self.buf[d:d + n] = self.core.rdram[src:src + n]

    def _resample(self, w1, w2):
        flags = (w1 >> 16) & 0xFF
        pitch = w1 & 0xFFFF
        self.resample(bool(flags & A_INIT), self.out, self.in_, (self.count + 15) & ~15, pitch << 1, self.addr(w2))

    def _savebuff(self, w1, w2):
        if self.count:
            n = (self.count + 15) & ~15
            dst = self.addr(w2) & ~7
            if self.saved is not None:
                self.saved.append((dst, n))
            s = self.out & 0xFFF
            n = min(n, 0x1000 - s)
            self.core.rdram[dst:dst + n] = self.buf[s:s + n]

    def _segment(self, w1, w2):
        self.segments[(w2 >> 24) & 0x3F] = w2 & 0xFFFFFF

    def _setbuff(self, w1, w2):
        flags = (w1 >> 16) & 0xFF
        if flags & A_AUX:
            self.dry_right = ((w1 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFFF
            self.wet_left = ((w2 >> 16) + ABI1_DMEM_BASE) & 0xFFFF
            self.wet_right = ((w2 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFFF
        else:
            self.in_ = ((w1 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFFF
            self.out = ((w2 >> 16) + ABI1_DMEM_BASE) & 0xFFFF
            self.count = w2 & 0xFFFF

    def _setvol(self, w1, w2):
        flags = (w1 >> 16) & 0xFF
        if flags & A_AUX:
            self.dry = _s16(w1); self.wet = _s16(w2)
        else:
            lr = 0 if flags & A_LEFT else 1
            if flags & A_VOL:
                self.vol[lr] = _s16(w1)
            else:
                self.target[lr] = _s16(w1); self.rate[lr] = _s32(w2)

    def _dmemmove(self, w1, w2):
        cnt = w2 & 0xFFFF
        if cnt:
            cnt = (cnt + 15) & ~15
            si = ((w1 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFF
            so = ((w2 >> 16) + ABI1_DMEM_BASE) & 0xFFF
            b = self.buf
            for k in range(cnt):  # forward byte copy (overlap semantics of the RSP loop)
                b[(so + k) & 0xFFF] = b[(si + k) & 0xFFF]

    def _loadadpcm(self, w1, w2):
        cnt = ((w1 & 0xFFFF) + 7) & ~7
        a = self.addr(w2)
        for k in range(min(cnt >> 1, 128)):
            self.table[k] = self._dram_s16(a + k * 2)

    def _mixer(self, w1, w2):
        if not self.count:
            return
        gain = _s16(w1)
        di = ((w2 >> 16) + ABI1_DMEM_BASE) & 0xFFFF
        do = ((w2 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFFF
        n = ((self.count + 31) & ~31) >> 1
        if USE_NUMPY and _np is not None:
            bo, bi = do & 0xFFE, di & 0xFFE
            if bo == bi and bo + 2 * n <= 0x1000 or self._disjoint((bo, bo + 2 * n), (bi, bi + 2 * n)):
                self._np_w16(bo, self._np_r16(bo, n) + ((self._np_r16(bi, n) * gain + 0x4000) >> 15))
                return
        rs, ws = self.rs16, self.ws16
        for k in range(n):
            # The ucode multiplies with rounding (VMULF-style), so round the Q15 product.
            ws(do + k * 2, _clamp16(rs(do + k * 2) + ((rs(di + k * 2) * gain + 0x4000) >> 15)))

    def _interleave(self, w1, w2):
        if not self.count:
            return
        left = ((w2 >> 16) + ABI1_DMEM_BASE) & 0xFFFF
        right = ((w2 & 0xFFFF) + ABI1_DMEM_BASE) & 0xFFFF
        n = ((self.count + 15) & ~15) >> 1   # samples per channel
        b = self.buf
        lv = bytes(b[left & 0xFFF:(left & 0xFFF) + n * 2])
        rv = bytes(b[right & 0xFFF:(right & 0xFFF) + n * 2])
        out = bytearray(n * 4)
        for k in range(min(n, len(lv) // 2, len(rv) // 2)):
            out[k * 4:k * 4 + 2] = lv[k * 2:k * 2 + 2]
            out[k * 4 + 2:k * 4 + 4] = rv[k * 2:k * 2 + 2]
        o = self.out & 0xFFF
        b[o:o + len(out)] = out[:0x1000 - o]

    def _polef(self, w1, w2):
        if not self.count:
            return
        flags = (w1 >> 16) & 0xFF
        self.polef(bool(flags & A_INIT), self.out, self.in_, (self.count + 15) & ~15, w1 & 0xFFFF, self.addr(w2))

    def _setloop(self, w1, w2):
        self.loop = self.addr(w2)

    _ABI1 = (_noop, _adpcm, _clearbuff, _envmixer, _loadbuff, _resample, _savebuff, _segment,
             _setbuff, _setvol, _dmemmove, _loadadpcm, _mixer, _interleave, _polef, _setloop)

    # ── DSP primitives ──
    def adpcm(self, init, loop, dmemo, dmemi, count, last_addr):
        table = self.table
        if init:
            last = [0] * 16
        else:
            src = self.loop if loop else last_addr
            last = [self._dram_s16(src + k * 2) for k in range(16)]
        b = self.buf
        ws = self.ws16
        for k in range(16):
            ws(dmemo, last[k]); dmemo += 2
        while count > 0:
            code = b[dmemi & 0xFFF]; dmemi += 1
            scale = code >> 4
            cb = (code & 0xF) << 4
            book1 = table[cb:cb + 8]; book2 = table[cb + 8:cb + 16]
            rshift = 12 - scale if scale < 12 else 0
            frame = []
            for _ in range(8):
                byte = b[dmemi & 0xFFF]; dmemi += 1
                hi = _s16((byte & 0xF0) << 8) >> rshift
                lo = _s16((byte & 0x0F) << 12) >> rshift
                frame.append(hi); frame.append(lo)
            for half in (0, 8):
                src = frame[half:half + 8]
                l1 = last[14] if half == 0 else last[6]
                l2 = last[15] if half == 0 else last[7]
                outv = [0] * 8
                for i in range(8):
                    acc = (src[i] << 11) + book1[i] * l1 + book2[i] * l2
                    for kk in range(i):
                        acc += book2[kk] * src[i - 1 - kk]
                    outv[i] = _clamp16(acc >> 11)
                last[half:half + 8] = outv
            for k in range(16):
                ws(dmemo, last[k]); dmemo += 2
            count -= 32
        for k in range(16):
            self._dram_w16(last_addr + k * 2, last[k])

    def resample(self, init, dmemo, dmemi, count, pitch, address):
        ipos = (dmemi >> 1) - 4
        opos = dmemo >> 1
        n = count >> 1
        rs, ws = self.rs16, self.ws16
        if init:
            for k in range(4):
                ws((ipos + k) * 2, 0)
            acc = 0
        else:
            for k in range(4):
                ws((ipos + k) * 2, self._dram_s16(address + k * 2))
            acc = self._dram_s16(address + 8) & 0xFFFF
        lut = self.lut
        if USE_NUMPY and _np is not None and n:
            # Sample k reads ipos0 + (T_k >> 16) with fraction T_k & 0xFFFF, T_k = acc0 + k * pitch.
            last_ipos = ipos + ((acc + (n - 1) * pitch) >> 16)
            if ipos >= 0 and self._disjoint((ipos * 2, last_ipos * 2 + 8), (opos * 2, opos * 2 + 2 * n)):
                np_ = _np
                lutn = getattr(self, "_lut_np", None)
                if lutn is None or self._lut_np_src is not lut:
                    lutn = self._lut_np = np_.array(lut, dtype=np_.int64); self._lut_np_src = lut
                T = acc + np_.arange(n, dtype=np_.int64) * pitch
                pos = (ipos + (T >> 16)) - ipos
                li = (T & 0xFC00) >> 8
                src = self._np_r16(ipos * 2, int(last_ipos - ipos) + 4)
                v = ((src[pos] * lutn[li]) >> 15) + ((src[pos + 1] * lutn[li + 1]) >> 15) + \
                    ((src[pos + 2] * lutn[li + 2]) >> 15) + ((src[pos + 3] * lutn[li + 3]) >> 15)
                self._np_w16(opos * 2, v)
                total = acc + n * pitch
                ipos += total >> 16
                acc = total & 0xFFFF
                n = 0
        for _ in range(n):
            li = (acc & 0xFC00) >> 8
            p = ipos * 2
            v = ((rs(p) * lut[li]) >> 15) + ((rs(p + 2) * lut[li + 1]) >> 15) + \
                ((rs(p + 4) * lut[li + 2]) >> 15) + ((rs(p + 6) * lut[li + 3]) >> 15)
            ws(opos * 2, _clamp16(v)); opos += 1
            acc += pitch
            ipos += acc >> 16
            acc &= 0xFFFF
        for k in range(4):
            self._dram_w16(address + k * 2, rs((ipos + k) * 2))
        self._dram_w16(address + 8, acc)

    def envmix_exp(self, init, aux, address):
        """ABI1 exponential volume envelope mixer into dry L/R (+ wet L/R when aux)."""
        rd = self.core.rdram
        a = address & 0xFFFFFC
        if init:
            dry, wet = self.dry, self.wet
            val = [self.vol[0] << 16, self.vol[1] << 16]
            tgt = [self.target[0] << 16, self.target[1] << 16]
            rates = [self.rate[0], self.rate[1]]
            seq = [_s32(self.vol[0] * self.rate[0]), _s32(self.vol[1] * self.rate[1])]
        else:
            # The ucode's 80-byte state: L/R per-lane volume ints (+frac lanes) for the last
            # 8 samples, then targetL(s16) rateL(s32) targetR(s16) rateR(s32) dry wet.
            li = _s16((rd[a + 14] << 8) | rd[a + 15]); lf = (rd[a + 30] << 8) | rd[a + 31]
            ri = _s16((rd[a + 46] << 8) | rd[a + 47]); rf = (rd[a + 62] << 8) | rd[a + 63]
            tl, rl, tr, rr, dry, wet = struct.unpack_from(">hihihh", rd, a + 64)
            val = [(li << 16) | lf, (ri << 16) | rf]
            tgt = [tl << 16, tr << 16]; rates = [rl, rr]
            seq = [_s32((val[0] * rates[0]) >> 16), _s32((val[1] * rates[1]) >> 16)]
        step = [tgt[0] - val[0], tgt[1] - val[1]]
        rs, ws = self.rs16, self.ws16
        dl, dr, wl, wr, src = self.out, self.dry_right, self.wet_left, self.wet_right, self.in_
        last_l = [0] * 8; last_r = [0] * 8
        lvs: List[int] = []; rvs: List[int] = []
        for _ in range(0, self.count, 16):
            # Ramp toward the current exponential point over 8 samples, then advance it (ucode order).
            for c in (0, 1):
                if step[c]:
                    step[c] = (seq[c] - val[c]) >> 3
            for _x in range(8):
                vols = []
                for c in (0, 1):
                    val[c] = _s32(val[c] + step[c])
                    # A zero step holds the volume (rate 1.0 sustains); only a moving ramp can arrive.
                    if step[c] and (val[c] <= tgt[c] if step[c] < 0 else val[c] >= tgt[c]):
                        val[c] = tgt[c]; step[c] = 0
                    vols.append(_s16(val[c] >> 16))
                lv, rv = vols
                last_l[_x] = lv; last_r[_x] = rv
                lvs.append(lv); rvs.append(rv)
            for c in (0, 1):
                if step[c]:
                    seq[c] = _s32((seq[c] * rates[c]) >> 16)
        n = len(lvs)
        outs = [dl & 0xFFE, dr & 0xFFE] + ([wl & 0xFFE, wr & 0xFFE] if aux else [])
        if n and USE_NUMPY and _np is not None and \
                self._disjoint((src & 0xFFE, (src & 0xFFE) + 2 * n), *[(o, o + 2 * n) for o in outs]):
            np_ = _np
            s_in = self._np_r16(src & 0xFFE, n)
            L = np_.array(lvs, dtype=np_.int64); R = np_.array(rvs, dtype=np_.int64)
            gains = [(L, dry), (R, dry)] + ([(L, wet), (R, wet)] if aux else [])
            for base, (vol, amt) in zip(outs, gains):
                gn = np_.clip((vol * amt + 0x4000) >> 15, -32768, 32767)
                self._np_w16(base, self._np_r16(base, n) + ((s_in * gn + 0x4000) >> 15))
        else:
            rs, ws = self.rs16, self.ws16
            for ptr in range(n):
                lv = lvs[ptr]; rv = rvs[ptr]
                s_in = rs(src + ptr * 2)
                g0 = _clamp16((lv * dry + 0x4000) >> 15); g1 = _clamp16((rv * dry + 0x4000) >> 15)
                o = ptr * 2
                ws(dl + o, _clamp16(rs(dl + o) + ((s_in * g0 + 0x4000) >> 15)))
                ws(dr + o, _clamp16(rs(dr + o) + ((s_in * g1 + 0x4000) >> 15)))
                if aux:
                    g2 = _clamp16((lv * wet + 0x4000) >> 15); g3 = _clamp16((rv * wet + 0x4000) >> 15)
                    ws(wl + o, _clamp16(rs(wl + o) + ((s_in * g2 + 0x4000) >> 15)))
                    ws(wr + o, _clamp16(rs(wr + o) + ((s_in * g3 + 0x4000) >> 15)))
        if a + 80 <= len(rd):
            frac_l = [0] * 7 + [val[0] & 0xFFFF]; frac_r = [0] * 7 + [val[1] & 0xFFFF]
            struct.pack_into(">8h8H8h8H", rd, a, *[_s16(v) for v in last_l], *frac_l,
                             *[_s16(v) for v in last_r], *frac_r)
            struct.pack_into(">hihihh", rd, a + 64, _s16(tgt[0] >> 16), _s32(rates[0]), _s16(tgt[1] >> 16),
                             _s32(rates[1]), _s16(dry), _s16(wet))

    def polef(self, init, dmemo, dmemi, count, gain, address):
        gain = _s16(gain)
        h1 = self.table[0:8]
        h2_before = self.table[8:16]
        h2 = [(_s16(x) * gain) >> 14 for x in h2_before]
        if init:
            l1 = l2 = 0
        else:
            l1 = self._dram_s16(address + 4); l2 = self._dram_s16(address + 6)
        rs, ws = self.rs16, self.ws16
        while count > 0:
            frame = [rs(dmemi + i * 2) for i in range(8)]
            dmemi += 16
            outv = []
            for i in range(8):
                acc = frame[i] * gain + h1[i] * l1 + h2_before[i] * l2
                for kk in range(i):
                    acc += h2[kk] * frame[i - 1 - kk]
                outv.append(_clamp16(acc >> 14))
            for i in range(8):
                ws(dmemo + i * 2, outv[i])
            l1, l2 = outv[6], outv[7]
            dmemo += 16
            count -= 16
        for k in range(4):
            self._dram_w16(address + k * 2, rs(dmemo - 8 + k * 2))


# ── Block recompiler: MIPS basic blocks → Python functions (accurate mode) ──
_JIT_MAX_BLOCK = 48
_M32 = "0xFFFFFFFF"
_M64 = "0xFFFFFFFFFFFFFFFF"


def _sx32(expr: str) -> str:
    """Python expression: sign-extend a 32-bit value to the 64-bit register encoding."""
    return f"((({expr}) ^ 0x80000000) - 0x80000000) & {_M64}"


class BlockJIT:
    """Compiles straight-line MIPS blocks (ending after a branch + delay slot) to Python.

    Each block returns the number of instructions it retired. Exceptions stay precise: inline
    memory ops record the faulting PC, and handler fallbacks abort the block when they redirect
    the PC. Blocks are invalidated on stores/DMA into their 4 KB pages and on TLB changes.
    """

    # Ops that end a block after executing (status/TLB/exception changes).
    _END_AFTER = {"MTC0", "DMTC0", "CTC0", "TLBWI", "TLBWR", "TLBR", "TLBP", "ERET", "SYSCALL", "BREAK",
                  "CACHE", "CTC1", "PATCH", "GROUP"}

    def __init__(self, core):
        self.core = core
        self.blocks: Dict[int, Any] = {}
        self.page_blocks: Dict[int, set] = {}
        self.mapped: set = set()          # vaddrs of blocks in TLB-mapped space
        self.compiled = 0
        self.invalidations = 0

    def clear(self):
        self.blocks.clear(); self.page_blocks.clear(); self.mapped.clear()

    def invalidate_page(self, page: int):
        keys = self.page_blocks.pop(page, None)
        if keys:
            self.invalidations += 1
            for k in keys:
                self.blocks.pop(k, None)
                self.mapped.discard(k)

    def invalidate_range(self, phys: int, length: int):
        if not self.page_blocks or length <= 0:
            return
        for page in range((phys & 0x1FFFFFFF) >> 12, (((phys & 0x1FFFFFFF) + length - 1) >> 12) + 1):
            if page in self.page_blocks:
                self.invalidate_page(page)

    def invalidate_mapped(self):
        for k in list(self.mapped):
            self.blocks.pop(k, None)
        self.mapped.clear()

    # ── compilation ──
    def compile(self, pc: int):
        bus = self.core.bus
        words = []
        addr = pc
        while len(words) < _JIT_MAX_BLOCK:
            try:
                w = bus.read_u32(addr)
            except TLBException:
                break
            o = get_opcode(w)
            if _DISPATCH[o.instr_id] is None:
                break  # unimplemented: let the interpreter raise RI/CpU precisely
            name = _INSTR_NAME.get(o.instr_id, "")
            if name in _JIT_BRANCHES:
                try:
                    dw = bus.read_u32((addr + 4) & MASK_32)
                except TLBException:
                    break
                if _DISPATCH[get_opcode(dw).instr_id] is None:
                    break
                words.append((addr, w)); words.append(((addr + 4) & MASK_32, dw))
                break
            words.append((addr, w))
            if name in self._END_AFTER:
                break
            addr = (addr + 4) & MASK_32
        if not words:
            return None
        fn = self._emit(words)
        if fn is None:
            return None
        phys = bus.v_to_p(pc) if not (0x80000000 <= pc < 0xC0000000) else pc & 0x1FFFFFFF
        last_phys = (phys + 4 * (len(words) - 1)) & 0x1FFFFFFF
        for page in {phys >> 12, last_phys >> 12}:
            self.page_blocks.setdefault(page, set()).add(pc)
        if not (0x80000000 <= pc < 0xC0000000):
            self.mapped.add(pc)
        self.blocks[pc] = fn
        self.compiled += 1
        return fn

    def _alt_block(self, words, fr: bool):
        """Lazily compiled variant of a block for the other Status.FR mode."""
        holder: List[Any] = []
        def alt(cpu, g):
            if not holder:
                holder.append(self._emit(words, fr))
            return holder[0](cpu, g)
        return alt

    def _emit(self, words, fr: Optional[bool] = None):
        if fr is None:
            fr = bool(self.core.cpu.cp0[CP0_STATUS] & STATUS_FR)
        self._fr = fr
        self._fpu_used = False
        self._cu1_done = False    # CU1 cannot change inside a block: one guard per block suffices
        self._fcr_clean = False   # FCR31 cause bits already cleared and not touched since
        L = []
        consts: Dict[str, Any] = {}
        def const(name, val):
            consts[name] = val
            return name
        L.append("def blk(cpu, g):")
        L.append(" ip = 0")
        L.append(" try:")
        body = []
        n = len(words)
        k = 0
        i = 0
        while i < n:
            addr, w = words[i]
            o = get_opcode(w)
            name = _INSTR_NAME.get(o.instr_id, "")
            if name in _JIT_BRANCHES:
                delay = words[i + 1] if i + 1 < n else None
                self._emit_branch(body, const, name, o, addr, delay, i)
                i += 2
                break
            stop = self._emit_one(body, const, name, o, addr, i, in_delay=False)
            i += 1
            if stop:
                break
        else:
            # Ran out of words without a branch: continue at the next instruction.
            nxt = (words[-1][0] + 4) & MASK_32
            body.append(f"cpu.pc = {nxt}; cpu.next_pc = {(nxt + 4) & MASK_32}")
            body.append(f"return {n}")
        if not body or not body[-1].startswith("return"):
            last = words[min(i, n) - 1][0]
            nxt = (last + 4) & MASK_32
            body.append(f"cpu.pc = {nxt}; cpu.next_pc = {(nxt + 4) & MASK_32}")
            body.append(f"return {min(i, n)}")
        for ln in body:
            L.append("  " + ln)
        if self._fpu_used:
            # FPU register access is specialised for the Status.FR mode the block was compiled in.
            L.insert(1, f" if (cpu.cp0[12] & {STATUS_FR}) != {STATUS_FR if fr else 0}: return ALT(cpu, g)")
            L.insert(2, " F = cpu.fpr; CU1 = cpu.cp0[12] & 0x20000000")
            consts["ALT"] = self._alt_block(words, not fr)
        L.append(" except TLBException as e:")
        L.append("  cpu.in_delay = ip < 0")
        L.append("  ipc = -ip if ip < 0 else ip")
        L.append("  cpu._tlb_exception(e, ipc)")
        L.append(f"  return IDX[ipc]")
        src = "\n".join(L)
        env = {"TLBException": TLBException, "MASK_32": MASK_32, "core": self.core, "rd": self.core.rdram,
               "B2F": bits_to_f32, "F2B": f32_to_bits, "SQRT": math.sqrt, "NAN": float("nan"),
               "PI": _S_U32.pack, "UF": _S_F32.unpack, "PQ": _S_U64.pack, "UD": _S_F64.unpack,
               "PD": _S_F64.pack, "UQ": _S_U64.unpack, "RQ": _S_U64.unpack_from, "WQ": _S_U64.pack_into,
               "RL": _S_U32.unpack_from, "WL": _S_U32.pack_into, "RH": _S_U16.unpack_from, "WH": _S_U16.pack_into,
               "FTOI": _fp_to_int, "FCMP": _fp_cmp,
               "bus": self.core.bus, "PB": self.page_blocks, "JIT": self,
               "IDX": {a: j + 1 for j, (a, _) in enumerate(words)}}
        env.update(consts)
        ns: Dict[str, Any] = {}
        try:
            exec(compile(src, f"<jit {words[0][0]:08X}>", "exec"), env, ns)
        except SyntaxError:  # pragma: no cover - generator bug; fall back to interpreter
            self.core.note_unimpl("jit:syntax")
            return None
        return ns["blk"]

    # Expressions for GPR reads (r0 is always 0).
    @staticmethod
    def _r(r):
        return "0" if r == 0 else f"g[{r}]"

    def _addr(self, o):
        if o.simm == 0:
            return f"({self._r(o.rs)} & {_M32})"
        return f"(({self._r(o.rs)} + {o.simm}) & {_M32})"

    def _load(self, body, o, addr, kind, delay, dst=None):
        """Inline RDRAM (KSEG0/1) load fast path; slow path via the bus. ``dst`` formats the store."""
        rt = o.rt
        tag = -addr if delay else addr
        body.append(f"ip = {tag}")
        body.append(f"a = {self._addr(o)}")
        fast = {
            "LW": ("p = a & 0x7FFFFC", "v = RL(rd, p)[0]", _sx32("v"), "bus.read_u32(a)"),
            "LWU": ("p = a & 0x7FFFFC", "v = RL(rd, p)[0]", "v", "bus.read_u32(a)"),
            "LH": ("p = a & 0x7FFFFE", "v = RH(rd, p)[0]", f"((v ^ 0x8000) - 0x8000) & {_M64}", "bus.read_u16(a)"),
            "LHU": ("p = a & 0x7FFFFE", "v = RH(rd, p)[0]", "v", "bus.read_u16(a)"),
            "LB": ("p = a & 0x7FFFFF", "v = rd[p]", f"((v ^ 0x80) - 0x80) & {_M64}", "bus.read_u8(a)"),
            "LBU": ("p = a & 0x7FFFFF", "v = rd[p]", "v", "bus.read_u8(a)"),
        }[kind]
        pset, vget, conv, slow = fast
        body.append("if 0x80000000 <= a < 0x80800000 or 0xA0000000 <= a < 0xA0800000:")
        body.append(f" {pset}; {vget}")
        body.append("else:")
        body.append(f" v = {slow}")
        if dst is not None:
            body.append(dst.format(conv))
        elif rt:
            body.append(f"g[{rt}] = {conv}")

    def _store(self, body, o, addr, kind, delay, val=None):
        tag = -addr if delay else addr
        body.append(f"ip = {tag}")
        body.append(f"a = {self._addr(o)}")
        v = self._r(o.rt) if val is None else val
        body.append("if 0x80000000 <= a < 0x80800000 or 0xA0000000 <= a < 0xA0800000:")
        if kind == "SW":
            body.append(f" p = a & 0x7FFFFC; WL(rd, p, ({v}) & {_M32})")
            slow = f"bus.write_u32(a, {v} & {_M32})"
        elif kind == "SH":
            body.append(f" p = a & 0x7FFFFE; WH(rd, p, ({v}) & 0xFFFF)")
            slow = f"bus.write_u16(a, {v} & 0xFFFF)"
        else:
            body.append(f" p = a & 0x7FFFFF; rd[p] = {v} & 255")
            slow = f"bus.write_u8(a, {v} & 255)"
        body.append(" if (p >> 12) in PB: JIT.invalidate_page(p >> 12)")
        body.append("else:")
        body.append(" " + slow)

    def _emit_one(self, body, const, name, o, addr, idx, in_delay) -> bool:
        """Emit one non-branch instruction. Returns True if the block must end after it."""
        rs, rt, rd_, sa = o.rs, o.rt, o.rd, o.sa
        R = self._r
        imm, simm = o.imm, o.simm
        if name == "NOP" or (o.word == 0):
            return False
        if name == "LUI":
            if rt: body.append(f"g[{rt}] = {u64(sign32(imm << 16))}")
        elif name in ("ADDIU", "ADDI"):
            if rt: body.append(f"g[{rt}] = " + _sx32(f"({R(rs)} + {simm}) & {_M32}"))
        elif name == "ORI":
            if rt: body.append(f"g[{rt}] = {R(rs)} | {imm}")
        elif name == "ANDI":
            if rt: body.append(f"g[{rt}] = {R(rs)} & {imm}")
        elif name == "XORI":
            if rt: body.append(f"g[{rt}] = {R(rs)} ^ {imm}")
        elif name == "SLTI":
            if rt: body.append(f"g[{rt}] = 1 if ((({R(rs)}) ^ 0x8000000000000000) - 0x8000000000000000) < {simm} else 0")
        elif name == "SLTIU":
            if rt: body.append(f"g[{rt}] = 1 if {R(rs)} < {u64(simm)} else 0")
        elif name == "DADDIU":
            if rt: body.append(f"g[{rt}] = ({R(rs)} + {simm}) & {_M64}")
        elif name in ("SLL", "SRL", "SRA"):
            if rd_:
                if name == "SLL": body.append(f"g[{rd_}] = " + _sx32(f"({R(rt)} << {sa}) & {_M32}"))
                elif name == "SRL": body.append(f"g[{rd_}] = " + _sx32(f"({R(rt)} & {_M32}) >> {sa}"))
                else: body.append(f"g[{rd_}] = " + _sx32(f"(((({R(rt)} & {_M32}) ^ 0x80000000) - 0x80000000) >> {sa}) & {_M32}"))
        elif name in ("SLLV", "SRLV", "SRAV"):
            if rd_:
                sh = f"({R(rs)} & 31)"
                if name == "SLLV": body.append(f"g[{rd_}] = " + _sx32(f"({R(rt)} << {sh}) & {_M32}"))
                elif name == "SRLV": body.append(f"g[{rd_}] = " + _sx32(f"({R(rt)} & {_M32}) >> {sh}"))
                else: body.append(f"g[{rd_}] = " + _sx32(f"(((({R(rt)} & {_M32}) ^ 0x80000000) - 0x80000000) >> {sh}) & {_M32}"))
        elif name in ("ADDU", "ADD"):
            if rd_: body.append(f"g[{rd_}] = " + _sx32(f"({R(rs)} + {R(rt)}) & {_M32}"))
        elif name in ("SUBU", "SUB"):
            if rd_: body.append(f"g[{rd_}] = " + _sx32(f"({R(rs)} - {R(rt)}) & {_M32}"))
        elif name in ("DADDU", "DADD"):
            if rd_: body.append(f"g[{rd_}] = ({R(rs)} + {R(rt)}) & {_M64}")
        elif name in ("DSUBU", "DSUB"):
            if rd_: body.append(f"g[{rd_}] = ({R(rs)} - {R(rt)}) & {_M64}")
        elif name == "AND":
            if rd_: body.append(f"g[{rd_}] = {R(rs)} & {R(rt)}")
        elif name == "OR":
            if rd_: body.append(f"g[{rd_}] = {R(rs)} | {R(rt)}")
        elif name == "XOR":
            if rd_: body.append(f"g[{rd_}] = {R(rs)} ^ {R(rt)}")
        elif name == "NOR":
            if rd_: body.append(f"g[{rd_}] = ~({R(rs)} | {R(rt)}) & {_M64}")
        elif name == "SLT":
            if rd_: body.append(f"g[{rd_}] = 1 if ((({R(rs)}) ^ 0x8000000000000000) - 0x8000000000000000) < ((({R(rt)}) ^ 0x8000000000000000) - 0x8000000000000000) else 0")
        elif name == "SLTU":
            if rd_: body.append(f"g[{rd_}] = 1 if {R(rs)} < {R(rt)} else 0")
        elif name == "MFHI":
            if rd_: body.append(f"g[{rd_}] = cpu.hi")
        elif name == "MFLO":
            if rd_: body.append(f"g[{rd_}] = cpu.lo")
        elif name == "MTHI":
            body.append(f"cpu.hi = {R(rs)}")
        elif name == "MTLO":
            body.append(f"cpu.lo = {R(rs)}")
        elif name == "MULTU":
            body.append(f"pr = ({R(rs)} & {_M32}) * ({R(rt)} & {_M32})")
            body.append("cpu.lo = " + _sx32(f"pr & {_M32}") + "; cpu.hi = " + _sx32(f"(pr >> 32) & {_M32}"))
        elif name == "MULT":
            s_ = lambda r: f"((({R(r)} & {_M32}) ^ 0x80000000) - 0x80000000)"
            body.append(f"pr = {s_(rs)} * {s_(rt)}")
            body.append("cpu.lo = " + _sx32(f"pr & {_M32}") + "; cpu.hi = " + _sx32(f"(pr >> 32) & {_M32}"))
        elif name in ("LW", "LWU", "LH", "LHU", "LB", "LBU"):
            self._load(body, o, addr, name, in_delay)
        elif name in ("SW", "SH", "SB"):
            self._store(body, o, addr, name, in_delay)
        elif name == "LD":
            self._load64(body, o, addr, in_delay, f"g[{rt}] = {{}}" if rt else None, masked_slow=False)
        elif name == "SD":
            self._store64(body, o, addr, in_delay, R(rt))
        elif name == "CACHE":
            nxt = (addr + 4) & MASK_32
            body.append(f"cpu.pc = {nxt}; cpu.next_pc = {(nxt + 4) & MASK_32}; cpu.in_delay = {in_delay}")
            body.append(f"return IDX[{addr}]")
            return True
        elif self._emit_fpu(body, const, name, o, addr, idx, in_delay):
            pass
        else:
            # Generic fallback: the interpreter handler with interpreter-equivalent PC state.
            self._fcr_clean = False   # handlers may write FCR31
            h = const(f"H{idx}", _DISPATCH[o.instr_id])
            oo = const(f"O{idx}", o)
            tag = -addr if in_delay else addr
            nxt = (addr + 4) & MASK_32
            body.append(f"ip = {tag}")
            body.append(f"cpu.pc = {nxt}; cpu.next_pc = {(nxt + 4) & MASK_32}; cpu.in_delay = {in_delay}")
            body.append(f"{h}(cpu, {oo}, {addr}, g)")
            body.append("g[0] = 0")
            if name in self._END_AFTER or name in ("SC", "SCD", "LL", "LLD"):
                body.append(f"return IDX[{addr}]")
                return True
            # Exception or redirected PC inside the handler: abort the block here.
            body.append(f"if cpu.pc != {nxt}: return IDX[{addr}]")
        return False

    # FPR access specialised for Status.FR (o32 games run FR=0: odd fN is the high half of f(N-1)).
    def _fg32(self, i):
        self._fpu_used = True
        if self._fr or not (i & 1):
            return f"(F[{i}] & 0xFFFFFFFF)"
        return f"(F[{i - 1}] >> 32)"

    def _fs32(self, i, v):
        self._fpu_used = True
        if self._fr or not (i & 1):
            return f"_fv = {v}; F[{i}] = (F[{i}] & 0xFFFFFFFF00000000) | (_fv & 0xFFFFFFFF)"
        return f"_fv = {v}; F[{i - 1}] = (F[{i - 1}] & 0xFFFFFFFF) | ((_fv & 0xFFFFFFFF) << 32)"

    def _fg64(self, i):
        self._fpu_used = True
        return f"F[{i if self._fr else i & ~1}]"

    def _fs64(self, i, v):
        self._fpu_used = True
        return f"F[{i if self._fr else i & ~1}] = ({v}) & {_M64}"

    def _clear_cause(self, body):
        """FCR31 cause clear; skipped when no op since the last clear could have set cause bits."""
        if not self._fcr_clean:
            body.append("cpu.fcr31 &= ~0x3F000")
            self._fcr_clean = True

    def _cu1_guard(self, body, addr, in_delay):
        """Coprocessor-unusable check, identical to the interpreter's handler behaviour."""
        self._fpu_used = True
        if self._cu1_done:
            return
        self._cu1_done = True
        body.append("if not CU1:")
        body.append(f" cpu.pc = {(addr + 4) & MASK_32}; cpu.next_pc = {(addr + 8) & MASK_32}; cpu.in_delay = {in_delay}")
        body.append(f" cpu._raise_exception(11, {addr}, ce=1); return IDX[{addr}]")

    def _emit_fpu(self, body, const, name, o, addr, idx, in_delay) -> bool:
        """Inline the hot COP1 paths (single, double, word); return False to use the handler."""
        R = self._r
        iid = o.instr_id
        if name == "LWC1":
            self._cu1_guard(body, addr, in_delay)
            self._load(body, o, addr, "LWU", in_delay, dst=self._fs32(o.rt, "{}"))
            return True
        if name == "SWC1":
            self._cu1_guard(body, addr, in_delay)
            self._store(body, o, addr, "SW", in_delay, val=self._fg32(o.rt))
            return True
        if name == "LDC1":
            self._cu1_guard(body, addr, in_delay)
            self._load64(body, o, addr, in_delay, self._fs64(o.rt, "{}"), masked_slow=True)
            return True
        if name == "SDC1":
            self._cu1_guard(body, addr, in_delay)
            self._store64(body, o, addr, in_delay, self._fg64(o.rt))
            return True
        if name == "MTC1":
            self._cu1_guard(body, addr, in_delay)
            body.append(self._fs32(o.rd, R(o.rt)))
            return True
        if name == "MFC1":
            self._cu1_guard(body, addr, in_delay)
            if o.rt:
                body.append(f"g[{o.rt}] = " + _sx32(self._fg32(o.rd)))
            return True
        if (iid & 0xF0000) != _ID_FPU:
            return False
        fmt = (iid >> 6) & 3
        funct = iid & 0x3F
        fs, ft, fd = o.rd, o.rt, o.sa
        if fmt == _ID_FPU_W:
            if funct not in (0x20, 0x21):
                return False
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            wi = f"float((({self._fg32(fs)} ^ 0x80000000) - 0x80000000))"
            if funct == 0x20:   # CVT.S.W
                body.append(self._fs32(fd, f"F2B({wi})"))
            else:               # CVT.D.W
                body.append(self._fs64(fd, f"UQ(PD({wi}))[0]"))
            return True
        if fmt not in (_ID_FPU_S, _ID_FPU_D):
            return False
        dbl = fmt == _ID_FPU_D
        if dbl:
            A = f"UD(PQ({self._fg64(fs)}))[0]"; B = f"UD(PQ({self._fg64(ft)}))[0]"
            put = lambda v: self._fs64(fd, f"UQ(PD({v}))[0]")
        else:
            A = f"UF(PI({self._fg32(fs)}))[0]"; B = f"UF(PI({self._fg32(ft)}))[0]"
            put = lambda v: self._fs32(fd, f"F2B({v})")
        ops = {0x00: f"{A} + {B}", 0x01: f"{A} - {B}", 0x02: f"{A} * {B}", 0x05: f"abs({A})", 0x07: f"-({A})"}
        if funct in ops:
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(put(ops[funct]))
            return True
        if funct == 0x03:  # DIV: zero divisor goes through the exact handler (flags/inf/nan)
            self._cu1_guard(body, addr, in_delay)
            h = const(f"H{idx}", _DISPATCH[iid]); oo = const(f"O{idx}", o)
            body.append(f"_b = {B}")
            body.append(f"if _b != 0.0: cpu.fcr31 &= ~0x3F000; {put(f'{A} / _b')}")
            body.append(f"else: {h}(cpu, {oo}, {addr}, g)")
            self._fcr_clean = False   # the zero-divisor handler sets cause bits
            return True
        if funct == 0x04:  # SQRT
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(f"_a = {A}")
            body.append(put("SQRT(_a) if _a >= 0 else NAN"))
            return True
        if funct == 0x06:  # MOV
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(self._fs64(fd, self._fg64(fs)) if dbl else self._fs32(fd, self._fg32(fs)))
            return True
        if funct == 0x20 and dbl:  # CVT.S.D
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(self._fs32(fd, f"F2B({A})"))
            return True
        if funct == 0x21 and not dbl:  # CVT.D.S
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(self._fs64(fd, f"UQ(PD({A}))[0]"))
            return True
        if funct == 0x24 or 0x0C <= funct <= 0x0F:  # CVT.W (FCR31.RM) / ROUND/TRUNC/CEIL/FLOOR.W
            self._cu1_guard(body, addr, in_delay)
            mode = "cpu.fcr31 & 3" if funct == 0x24 else str(funct - 0x0C)
            self._clear_cause(body)
            body.append(self._fs32(fd, f"FTOI({A}, {mode}, 32)"))
            return True
        if funct >= 0x30:  # C.cond
            self._cu1_guard(body, addr, in_delay)
            self._clear_cause(body)
            body.append(f"if FCMP({A}, {B}, {funct}): cpu.fcr31 |= 0x800000")
            body.append("else: cpu.fcr31 &= ~0x800000")
            return True
        return False

    def _load64(self, body, o, addr, delay, dst, masked_slow):
        """Inline 64-bit RDRAM load (KSEG0/1); slow path via bus.read_u64 exactly like the handler."""
        tag = -addr if delay else addr
        body.append(f"ip = {tag}")
        body.append(f"a = {self._addr(o)}")
        body.append("if 0x80000000 <= a < 0x807FFFF9 or 0xA0000000 <= a < 0xA07FFFF9:")
        body.append(" v = RQ(rd, a & 0x7FFFFF)[0]")
        body.append("else:")
        body.append(" v = bus.read_u64(" + ("a" if masked_slow else f"{self._r(o.rs)} + {o.simm}") + ")")
        if dst is not None:
            body.append(dst.format("v"))

    def _store64(self, body, o, addr, delay, val):
        """Inline 64-bit RDRAM store (two 32-bit halves, each with its JIT page check)."""
        tag = -addr if delay else addr
        body.append(f"ip = {tag}")
        body.append(f"a = {self._addr(o)}")
        body.append(f"v = {val}")
        body.append("if 0x80000000 <= a < 0x807FFFF9 or 0xA0000000 <= a < 0xA07FFFF9:")
        body.append(f" p = a & 0x7FFFFF; WQ(rd, p, v & {_M64})")
        body.append(" if (p >> 12) in PB: JIT.invalidate_page(p >> 12)")
        body.append(" if ((p + 4) >> 12) in PB: JIT.invalidate_page((p + 4) >> 12)")
        body.append("else:")
        body.append(" bus.write_u64(a, v)")

    def _emit_branch(self, body, const, name, o, addr, delay, idx):
        R = self._r
        rs, rt = o.rs, o.rt
        target = None
        likely = name in _JIT_LIKELY
        s64 = lambda r: f"((({R(r)}) ^ 0x8000000000000000) - 0x8000000000000000)"
        cond = None
        link = None
        if name in ("J", "JAL"):
            target = str(o.target_addr(addr))
            cond = "True"
            if name == "JAL": link = 31
        elif name in ("JR", "JALR"):
            body.append(f"tgt = {R(rs)} & {_M32}")
            target = "tgt"; cond = "True"
            if name == "JALR": link = o.rd
        else:
            target = str(o.branch_addr(addr))
            base = name[:-1] if likely else name
            if base in ("BEQ",): cond = f"{R(rs)} == {R(rt)}"
            elif base in ("BNE",): cond = f"{R(rs)} != {R(rt)}"
            elif base in ("BLEZ",): cond = f"{s64(rs)} <= 0"
            elif base in ("BGTZ",): cond = f"{s64(rs)} > 0"
            elif base in ("BLTZ", "BLTZAL"): cond = f"{s64(rs)} < 0"
            elif base in ("BGEZ", "BGEZAL"): cond = f"{s64(rs)} >= 0"
            elif base == "BC1F": cond = "not (cpu.fcr31 & 0x800000)"
            elif base == "BC1T": cond = "(cpu.fcr31 & 0x800000) != 0"
            else: cond = "False"
            if base in ("BLTZAL", "BGEZAL"): link = 31
        if name in ("BC1F", "BC1T", "BC1FL", "BC1TL"):
            body.append("if not (cpu.cp0[12] & 0x20000000):")
            body.append(f" cpu.pc = {addr}; cpu.next_pc = {(addr + 4) & MASK_32}; cpu.in_delay = False")
            body.append(f" cpu._raise_exception(11, {addr}, ce=1); return IDX[{addr}]")
        body.append(f"tk = {cond}")
        if link:
            body.append(f"g[{link}] = {(addr + 8) & MASK_32}")
        # Branch to self with an empty delay slot = idle loop (fast-forwarded by the scheduler).
        if name in ("BEQ", "J") and target == str(addr) and (delay is None or delay[1] == 0) and (name == "J" or rs == rt):
            body.append("cpu.idle = True")
        if delay is not None:
            dbody: List[str] = []
            dname = _INSTR_NAME.get(get_opcode(delay[1]).instr_id, "")
            if dname in _JIT_BRANCHES:
                dname = "NOP"  # branch in a delay slot is undefined; ignore it
                stop = False
            else:
                stop = self._emit_one(dbody, const, dname, get_opcode(delay[1]), delay[0], idx + 1, in_delay=True)
            if likely:
                if dbody:  # likely: delay slot only executes when the branch is taken
                    body.append("if tk:")
                    for ln in dbody:
                        body.append(" " + ln)
            else:
                body.extend(dbody)
        fall = (addr + 8) & MASK_32
        body.append(f"if tk: cpu.pc = {target}; cpu.next_pc = ({target} + 4) & {_M32}")
        body.append(f"else: cpu.pc = {fall}; cpu.next_pc = {(fall + 4) & MASK_32}")
        body.append(f"return IDX[{delay[0] if delay else addr}]")


_JIT_LIKELY = {"BEQL", "BNEL", "BLEZL", "BGTZL", "BLTZL", "BGEZL", "BLTZALL", "BGEZALL", "BC1FL", "BC1TL"}
_JIT_BRANCHES = {"J", "JAL", "JR", "JALR", "BEQ", "BNE", "BLEZ", "BGTZ", "BEQL", "BNEL", "BLEZL", "BGTZL",
                 "BLTZ", "BGEZ", "BLTZL", "BGEZL", "BLTZAL", "BGEZAL", "BLTZALL", "BGEZALL",
                 "BC1F", "BC1T", "BC1FL", "BC1TL"}


def _build_instr_names() -> Dict[int, str]:
    names: Dict[int, str] = {}
    for op, (name, fmt) in PRIMARY_OPS.items():
        if name not in ("SPECIAL", "REGIMM", "COP0", "COP1"):
            names[_ID_PRIMARY | op] = name
    for f, (n, _ff) in SPECIAL_OPS.items():
        names[_ID_SPECIAL | f] = n
    for rt, (n, _ff) in REGIMM_OPS.items():
        names[_ID_REGIMM | rt] = n
    for rs, (n, _ff) in COP0_RS.items():
        names[_ID_COP0_RS | rs] = n
    for cf, (cn, _cff) in COP0_CO.items():
        names[_ID_COP0_CO | cf] = cn
    for rs, (n, _ff) in COP1_RS.items():
        names[_ID_COP1_RS | rs] = n
    for rt, n in enumerate(("BC1F", "BC1T", "BC1FL", "BC1TL")):
        names[_ID_COP1_BC | rt] = n
    return names


_INSTR_NAME = _build_instr_names()


# ── LLE RSP: scalar unit + vector unit (runs any microcode; used when HLE does not know it) ──
def _rsp_build_tables():
    rcp = []
    for i in range(512):
        a = i + 512
        b = (1 << 34) // a
        rcp.append(((b + 1) >> 8) & 0xFFFF)
    rsq = []
    for i in range(512):
        a = (i + 512) >> (1 if i % 2 == 1 else 0)
        # Smallest m with a*m*m >= 2**44 (exact integer sqrt), i.e. the old b+=1 search's b = m-1.
        m = math.isqrt(-(-(1 << 44) // a))
        while a * m * m < (1 << 44):
            m += 1
        while m > 1 and a * (m - 1) * (m - 1) >= (1 << 44):
            m -= 1
        b = max(1 << 17, m - 1)
        rsq.append((b >> 1) & 0xFFFF)
    return rcp, rsq


_RSP_RCP_ROM, _RSP_RSQ_ROM = _rsp_build_tables()
# Element selector → source lane for each of the 8 lanes.
_RSP_ELEM = [[i for i in range(8)], [i for i in range(8)],
             [0, 0, 2, 2, 4, 4, 6, 6], [1, 1, 3, 3, 5, 5, 7, 7],
             [0, 0, 0, 0, 4, 4, 4, 4], [1, 1, 1, 1, 5, 5, 5, 5],
             [2, 2, 2, 2, 6, 6, 6, 6], [3, 3, 3, 3, 7, 7, 7, 7]] + [[e] * 8 for e in range(8)]


def _s16(v):
    v &= 0xFFFF
    return v - 0x10000 if v & 0x8000 else v


def _clz32(v):
    v &= MASK_32
    return 32 - v.bit_length()


def _rsp_rcp(inp, dp):
    if inp == 0:
        return 0x7FFFFFFF
    if inp == -32768 and not dp:
        return 0xFFFF0000
    data = -inp if inp < 0 else inp
    shift = _clz32(data)
    idx = ((data << shift) >> 22) & 0x1FF
    res = _RSP_RCP_ROM[idx]
    res = (((0x10000 | res) << 14) >> (31 - shift)) & MASK_32
    if inp < 0:
        res = ~res & MASK_32
    return res


def _rsp_rsq(inp, dp):
    if inp == 0:
        return 0x7FFFFFFF
    if inp == -32768 and not dp:
        return 0xFFFF0000
    data = -inp if inp < 0 else inp
    shift = _clz32(data)
    idx = (((data << shift) >> 23) & 0xFF) | ((shift & 1) << 8)
    res = _RSP_RSQ_ROM[idx]
    res = (((0x10000 | res) << 14) >> ((31 - shift) >> 1)) & MASK_32
    if inp < 0:
        res = ~res & MASK_32
    return res


class RSP:
    """Cycle-agnostic RSP interpreter. run() executes until BREAK (or the instruction budget)."""

    def __init__(self, core):
        self.core = core
        self.reset()

    def reset(self):
        self.r = [0] * 32
        self.pc = 0
        self.next_pc = 4
        self.vr = [[0] * 8 for _ in range(32)]   # 32 vector regs × 8 lanes, unsigned 16-bit
        self.acc = [0] * 8                       # 48-bit signed accumulators
        self.vco = 0; self.vcc = 0; self.vce = 0
        self.div_in = 0; self.div_out = 0; self.div_dp = False
        self.executed = 0
        self.decode_cache: Dict[int, Any] = {}

    # ── memory (DMEM, big-endian, wraps at 4 KB) ──
    def rb(self, a):
        return self.core.rsp_dmem[a & 0xFFF]

    def wb(self, a, v):
        self.core.rsp_dmem[a & 0xFFF] = v & 0xFF

    # ── COP0: SP and DP registers ──
    _C0 = (SP_MEM_ADDR, SP_DRAM_ADDR, SP_RD_LEN, SP_WR_LEN, SP_STATUS, SP_DMA_FULL, SP_DMA_BUSY, SP_SEMAPHORE,
           DPC_START, DPC_END, DPC_CURRENT, DPC_STATUS, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM)

    def mfc0(self, rd):
        bus = self.core.bus
        reg = self._C0[rd & 15]
        if reg == SP_SEMAPHORE:
            v = bus.regs.get(SP_SEMAPHORE, 0)
            bus.regs[SP_SEMAPHORE] = 1
            return v
        if reg == SP_STATUS:
            return bus.sp_status
        if reg == DPC_STATUS:
            return bus.dpc_status
        if reg in (SP_DMA_FULL, SP_DMA_BUSY, DPC_CLOCK, DPC_BUFBUSY, DPC_PIPEBUSY, DPC_TMEM):
            return 0
        return bus.regs.get(reg, 0)

    def mtc0(self, rd, v):
        bus = self.core.bus
        reg = self._C0[rd & 15]
        v &= MASK_32
        if reg == SP_SEMAPHORE:
            bus.regs[SP_SEMAPHORE] = 0
        elif reg == SP_STATUS:
            # RSP may change signals / interrupt; halting itself is done with BREAK.
            bus._change_sp_status(v & ~(SP_CLR_HALT))
        elif reg == DPC_STATUS:
            bus._change_dpc_status(v)
        elif reg == DPC_START:
            bus.regs[DPC_START] = v & 0xFFFFF8; bus.regs[DPC_CURRENT] = v & 0xFFFFF8
        elif reg == DPC_END:
            bus.regs[DPC_END] = v & 0xFFFFF8
            bus.regs[DPC_CURRENT] = self.core.process_rdp_commands(
                bus.regs.get(DPC_CURRENT, 0), v & 0xFFFFF8, xbus=bool(bus.dpc_status & DPC_STATUS_XBUS_DMEM_DMA))
        elif reg in (SP_MEM_ADDR, SP_DRAM_ADDR):
            bus.regs[reg] = v
        elif reg == SP_RD_LEN:
            bus.regs[reg] = v; self.core.trigger_sp_dma(to_rsp=True)
        elif reg == SP_WR_LEN:
            bus.regs[reg] = v; self.core.trigger_sp_dma(to_rsp=False)
        else:
            bus.regs[reg] = v

    # ── vector helpers ──
    def vt_e(self, vt, e):
        src = self.vr[vt]
        return [src[k] for k in _RSP_ELEM[e & 15]]

    def vbytes(self, v):
        out = bytearray(16)
        reg = self.vr[v]
        for i in range(8):
            out[i * 2] = reg[i] >> 8; out[i * 2 + 1] = reg[i] & 0xFF
        return out

    def vset_bytes(self, v, b):
        self.vr[v] = [(b[i * 2] << 8) | b[i * 2 + 1] for i in range(8)]

    # ── run ──
    def run(self, max_instr: int = 20_000_000) -> int:
        bus = self.core.bus
        imem = self.core.rsp_imem
        r = self.r
        n = 0
        pc = self.pc & 0xFFC
        npc = self.next_pc & 0xFFC
        while n < max_instr:
            if bus.sp_status & SP_STATUS_HALT:
                break
            w = (imem[pc] << 24) | (imem[pc + 1] << 16) | (imem[pc + 2] << 8) | imem[pc + 3]
            cur = pc
            pc = npc
            npc = (npc + 4) & 0xFFC
            self.pc, self.next_pc = pc, npc
            branch = self.step(w, cur)
            if branch is not None:
                npc = branch & 0xFFC
                self.next_pc = npc
            r[0] = 0
            n += 1
            if bus.sp_status & SP_STATUS_HALT:
                pc = self.pc
                break
        self.pc, self.next_pc = pc, npc
        self.executed += n
        if n >= max_instr:
            self.core.note_unimpl("rsp:budget-exceeded")
        return n

    def _break(self):
        bus = self.core.bus
        bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE
        if bus.sp_status & SP_STATUS_INTR_BREAK:
            if self.core.lle:
                self.core.schedule("SP", 100)
            else:
                bus.hw_interrupts |= MI_INTR_SP

    def step(self, w, cur):
        """Execute one RSP instruction; returns a branch target (taken branch/jump) or None."""
        r = self.r
        op = w >> 26
        rs = (w >> 21) & 31; rt = (w >> 16) & 31
        imm = w & 0xFFFF; simm = imm - 0x10000 if imm & 0x8000 else imm
        if op == 0:
            rd = (w >> 11) & 31; sa = (w >> 6) & 31; f = w & 63
            if f == 0x00: r[rd] = (r[rt] << sa) & MASK_32
            elif f == 0x02: r[rd] = (r[rt] & MASK_32) >> sa
            elif f == 0x03: r[rd] = (_s32(r[rt]) >> sa) & MASK_32
            elif f == 0x04: r[rd] = (r[rt] << (r[rs] & 31)) & MASK_32
            elif f == 0x06: r[rd] = (r[rt] & MASK_32) >> (r[rs] & 31)
            elif f == 0x07: r[rd] = (_s32(r[rt]) >> (r[rs] & 31)) & MASK_32
            elif f == 0x08: return r[rs]
            elif f == 0x09:
                t = r[rs]; r[rd] = (cur + 8) & 0xFFF; return t
            elif f == 0x0D: self._break()
            elif f in (0x20, 0x21): r[rd] = (r[rs] + r[rt]) & MASK_32
            elif f in (0x22, 0x23): r[rd] = (r[rs] - r[rt]) & MASK_32
            elif f == 0x24: r[rd] = r[rs] & r[rt]
            elif f == 0x25: r[rd] = r[rs] | r[rt]
            elif f == 0x26: r[rd] = r[rs] ^ r[rt]
            elif f == 0x27: r[rd] = ~(r[rs] | r[rt]) & MASK_32
            elif f == 0x2A: r[rd] = 1 if _s32(r[rs]) < _s32(r[rt]) else 0
            elif f == 0x2B: r[rd] = 1 if (r[rs] & MASK_32) < (r[rt] & MASK_32) else 0
            return None
        if op == 1:
            v = _s32(r[rs])
            tgt = (cur + 4 + (simm << 2)) & 0xFFF
            if rt in (0x10, 0x11):
                r[31] = (cur + 8) & 0xFFF
            if rt in (0x00, 0x10):
                return tgt if v < 0 else None
            if rt in (0x01, 0x11):
                return tgt if v >= 0 else None
            return None
        if op == 2: return (w & 0x3FF) << 2
        if op == 3:
            r[31] = (cur + 8) & 0xFFF
            return (w & 0x3FF) << 2
        if 4 <= op <= 7:
            tgt = (cur + 4 + (simm << 2)) & 0xFFF
            a = _s32(r[rs]); b = _s32(r[rt])
            take = (a == b) if op == 4 else (a != b) if op == 5 else (a <= 0) if op == 6 else (a > 0)
            return tgt if take else None
        if op in (8, 9): r[rt] = (r[rs] + simm) & MASK_32; return None
        if op == 0x0A: r[rt] = 1 if _s32(r[rs]) < simm else 0; return None
        if op == 0x0B: r[rt] = 1 if (r[rs] & MASK_32) < (simm & MASK_32) else 0; return None
        if op == 0x0C: r[rt] = r[rs] & imm; return None
        if op == 0x0D: r[rt] = r[rs] | imm; return None
        if op == 0x0E: r[rt] = r[rs] ^ imm; return None
        if op == 0x0F: r[rt] = (imm << 16) & MASK_32; return None
        if op == 0x10:  # COP0
            rd = (w >> 11) & 31
            if rs == 0x00: r[rt] = self.mfc0(rd)
            elif rs == 0x04: self.mtc0(rd, r[rt])
            return None
        if op == 0x12:  # COP2
            return self.cop2(w)
        a = (r[rs] + simm) & 0xFFF
        if op == 0x20: v = self.rb(a); r[rt] = (v - 0x100 if v & 0x80 else v) & MASK_32
        elif op == 0x21: v = (self.rb(a) << 8) | self.rb(a + 1); r[rt] = _s16(v) & MASK_32
        elif op == 0x23: r[rt] = (self.rb(a) << 24) | (self.rb(a + 1) << 16) | (self.rb(a + 2) << 8) | self.rb(a + 3)
        elif op == 0x24: r[rt] = self.rb(a)
        elif op == 0x25: r[rt] = (self.rb(a) << 8) | self.rb(a + 1)
        elif op == 0x27: r[rt] = (self.rb(a) << 24) | (self.rb(a + 1) << 16) | (self.rb(a + 2) << 8) | self.rb(a + 3)
        elif op == 0x28: self.wb(a, r[rt])
        elif op == 0x29: self.wb(a, r[rt] >> 8); self.wb(a + 1, r[rt])
        elif op == 0x2B:
            v = r[rt]
            self.wb(a, v >> 24); self.wb(a + 1, v >> 16); self.wb(a + 2, v >> 8); self.wb(a + 3, v)
        elif op == 0x32: self.lwc2(w)
        elif op == 0x3A: self.swc2(w)
        else:
            self.core.note_unimpl(f"rsp:op{op:02X}")
        return None

    # ── COP2 moves + vector ops ──
    def cop2(self, w):
        rs = (w >> 21) & 31; rt = (w >> 16) & 31; rd = (w >> 11) & 31
        r = self.r
        if not (rs & 0x10):
            e = (w >> 7) & 15
            if rs == 0x00:   # MFC2 rt, vd[e]
                b = self.vbytes(rd)
                r[rt] = _s16((b[e & 15] << 8) | b[(e + 1) & 15]) & MASK_32
            elif rs == 0x04: # MTC2
                b = self.vbytes(rd)
                v = r[rt]
                b[e & 15] = (v >> 8) & 0xFF
                if e < 15:
                    b[e + 1] = v & 0xFF
                self.vset_bytes(rd, b)
            elif rs == 0x02: # CFC2
                v = (self.vco, self.vcc, self.vce)[rd & 3] if (rd & 3) < 3 else self.vce
                r[rt] = _s16(v) & MASK_32
            elif rs == 0x06: # CTC2
                v = r[rt] & 0xFFFF
                if (rd & 3) == 0: self.vco = v
                elif (rd & 3) == 1: self.vcc = v
                else: self.vce = v & 0xFF
            return None
        f = w & 63
        e = (w >> 21) & 15
        vt = rt; vs = rd; vd = (w >> 6) & 31
        fn = _RSP_VOPS.get(f)
        if fn is None:
            self.core.note_unimpl(f"rsp:vop{f:02X}")
            return None
        fn(self, vd, vs, vt, e)
        return None

    # ── vector loads / stores (LWC2 / SWC2) ──
    _VLS_SHIFT = (0, 1, 2, 3, 4, 4, 3, 3, 4, 4, 4, 4)

    def lwc2(self, w):
        base = (w >> 21) & 31; vt = (w >> 16) & 31; kind = (w >> 11) & 31
        e = (w >> 7) & 15
        off = w & 0x7F
        if off & 0x40: off -= 0x80
        if kind >= 12:
            self.core.note_unimpl(f"rsp:lwc2:{kind}")
            return
        a = (self.r[base] + (off << self._VLS_SHIFT[kind])) & 0xFFF
        b = self.vbytes(vt)
        if kind <= 3:   # LBV LSV LLV LDV
            n = 1 << kind
            for i in range(n):
                if e + i < 16:
                    b[e + i] = self.rb(a + i)
        elif kind == 4:  # LQV
            end = (a & ~15) + 16
            i = e
            while a < end and i < 16:
                b[i] = self.rb(a); a += 1; i += 1
        elif kind == 5:  # LRV
            start = a & ~15
            i = 16 - (a & 15) + e
            x = start
            while x < a:
                if i < 16:
                    b[i] = self.rb(x)
                x += 1; i += 1
        elif kind in (6, 7):  # LPV / LUV: bytes into lane upper bits (signed <<8 / unsigned <<7)
            ab = a & ~7
            sh = 8 if kind == 6 else 7
            lanes = []
            for i in range(8):
                byte = self.rb(ab + (((a & 7) - e + i) & 15))
                lanes.append((byte << sh) & 0xFFFF)
            self.vr[vt] = lanes
            return
        elif kind == 8:  # LHV
            ab = a & ~7
            lanes = []
            for i in range(8):
                byte = self.rb(ab + (((a & 7) - e + i * 2) & 15))
                lanes.append((byte << 7) & 0xFFFF)
            self.vr[vt] = lanes
            return
        elif kind == 9:  # LFV
            ab = a & ~7
            tmp = []
            for i in range(4):
                byte = self.rb(ab + (((a & 7) - e + i * 4) & 15))
                tmp.append((byte << 7) & 0xFFFF)
            for i in range(4):
                byte = self.rb(ab + (((a & 7) - e + i * 4 + 8) & 15))
                tmp.append((byte << 7) & 0xFFFF)
            lanes = list(self.vr[vt])
            start = e >> 1
            for i in range(start, min(start + 4, 8)):
                lanes[i] = tmp[i]
            self.vr[vt] = lanes
            return
        elif kind == 11:  # LTV: transpose into 8 registers
            vbase = vt & ~7
            ab = a & ~7
            for i in range(8):
                reg = vbase + ((i + (e >> 1)) & 7)
                hb = self.rb(ab + ((i * 2 + e + (a & 8)) & 15))
                lb = self.rb(ab + ((i * 2 + e + 1 + (a & 8)) & 15))
                lanes = list(self.vr[reg]); lanes[i] = (hb << 8) | lb; self.vr[reg] = lanes
            return
        else:
            self.core.note_unimpl(f"rsp:lwc2:{kind}")
            return
        self.vset_bytes(vt, b)

    def swc2(self, w):
        base = (w >> 21) & 31; vt = (w >> 16) & 31; kind = (w >> 11) & 31
        e = (w >> 7) & 15
        off = w & 0x7F
        if off & 0x40: off -= 0x80
        if kind >= 12:
            self.core.note_unimpl(f"rsp:swc2:{kind}")
            return
        a = (self.r[base] + (off << self._VLS_SHIFT[kind])) & 0xFFF
        b = self.vbytes(vt)
        if kind <= 3:   # SBV SSV SLV SDV
            for i in range(1 << kind):
                self.wb(a + i, b[(e + i) & 15])
        elif kind == 4:  # SQV
            end = (a & ~15) + 16
            i = e
            while a < end:
                self.wb(a, b[i & 15]); a += 1; i += 1
        elif kind == 5:  # SRV
            start = a & ~15
            i = 16 - (a & 15) + e
            x = start
            while x < a:
                self.wb(x, b[i & 15]); x += 1; i += 1
        elif kind in (6, 7):  # SPV / SUV
            ab = a & ~7
            lanes = self.vr[vt]
            for i in range(8):
                j = (e + i) & 15
                lane = lanes[j & 7]
                if kind == 6:
                    val = (lane >> 8) if j < 8 else (lane >> 7)
                else:
                    val = (lane >> 7) if j < 8 else (lane >> 8)
                self.wb(ab + ((a & 7) + i), val)
        elif kind == 8:  # SHV
            ab = a & ~7
            lanes = self.vr[vt]
            for i in range(8):
                j = (e >> 1) + i
                val = (lanes[j & 7] >> 7) & 0xFF
                self.wb(ab + (((a & 7) + i * 2) & 15), val)
        elif kind == 9:  # SFV
            ab = a & ~7
            lanes = self.vr[vt]
            idx = {0: (0, 1, 2, 3), 8: (4, 5, 6, 7), 4: (1, 2, 3, 0), 12: (5, 6, 7, 4)}.get(e)
            if idx:
                for i, j in enumerate(idx):
                    self.wb(ab + (((a & 7) + i * 4) & 15), (lanes[j] >> 7) & 0xFF)
        elif kind == 10:  # SWV
            ab = a & ~7
            for i in range(16):
                self.wb(ab + (((a & 7) + i) & 15), b[(e + i) & 15])
        elif kind == 11:  # STV
            vbase = vt & ~7
            ab = a & ~7
            start = e >> 1
            for i in range(8):
                reg = vbase + ((start + i) & 7)
                lane = self.vr[reg][i]
                o = ((a & 7) + i * 2) & 15
                self.wb(ab + o, lane >> 8); self.wb(ab + ((o + 1) & 15), lane)


def _acc_set(acc, i, v):
    v &= 0xFFFFFFFFFFFF
    acc[i] = v - 0x1000000000000 if v & 0x800000000000 else v


def _sclamp_mid(acc_v):
    """Signed clamp of accumulator bits 47..16 to a 16-bit result (mid)."""
    hi = acc_v >> 16
    if hi < -32768: return 0x8000
    if hi > 32767: return 0x7FFF
    return hi & 0xFFFF


def _uclamp_low(acc_v):
    """Low 16 bits, clamped when bits 47..16 do not sign-extend bit 15."""
    hi = acc_v >> 16
    if hi < -32768: return 0x0000
    if hi > 32767: return 0xFFFF
    return acc_v & 0xFFFF


def _v_mul(signed_s, signed_t, frac, accumulate, result):
    def op(rsp, vd, vs, vt, e):
        s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
        out = [0] * 8
        for i in range(8):
            a = _s16(s[i]) if signed_s else s[i]
            b = _s16(t[i]) if signed_t else t[i]
            if frac == "f":
                p = (a * b) << 1
                v = (acc[i] + p) if accumulate else (p + 0x8000)
            elif frac == "l":
                p = (a * b) >> 16
                v = (acc[i] + p) if accumulate else p
            elif frac == "h":
                p = (a * b) << 16
                v = (acc[i] + p) if accumulate else p
            else:  # "m" / "n": plain product at the mid/low position
                p = a * b
                v = (acc[i] + p) if accumulate else p
            _acc_set(acc, i, v)
            av = acc[i]
            if result == "s":     # signed clamp of mid
                out[i] = _sclamp_mid(av)
            elif result == "l":   # low with clamp
                out[i] = _uclamp_low(av)
        rsp.vr[vd] = out
    return op


def _v_mulf_special(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8
    for i in range(8):
        a = _s16(s[i]); b = _s16(t[i])
        _acc_set(acc, i, ((a * b) << 1) + 0x8000)
        out[i] = 0x7FFF if (a == -32768 and b == -32768) else _sclamp_mid(acc[i])
    rsp.vr[vd] = out


def _v_mulu(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8
    for i in range(8):
        a = _s16(s[i]); b = _s16(t[i])
        _acc_set(acc, i, ((a * b) << 1) + 0x8000)
        hi = acc[i] >> 16
        out[i] = 0 if hi < 0 else (0xFFFF if hi > 0x7FFF else hi)
    rsp.vr[vd] = out


def _v_macu(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8
    for i in range(8):
        _acc_set(acc, i, acc[i] + ((_s16(s[i]) * _s16(t[i])) << 1))
        hi = acc[i] >> 16
        out[i] = 0 if hi < 0 else (0xFFFF if hi > 0x7FFF else hi)
    rsp.vr[vd] = out


def _set_acc_lo(acc, i, v):
    _acc_set(acc, i, (acc[i] & ~0xFFFF) | (v & 0xFFFF))


def _v_addsub(sub):
    def op(rsp, vd, vs, vt, e):
        s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
        out = [0] * 8
        for i in range(8):
            c = (rsp.vco >> i) & 1
            a = _s16(s[i]); b = _s16(t[i])
            res = a - b - c if sub else a + b + c
            _set_acc_lo(acc, i, res)
            out[i] = 0x7FFF if res > 32767 else (0x8000 if res < -32768 else res & 0xFFFF)
        rsp.vco = 0
        rsp.vr[vd] = out
    return op


def _v_abs(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8
    for i in range(8):
        a = _s16(s[i]); b = _s16(t[i])
        if a < 0:
            if b == -32768:
                out[i] = 0x7FFF; _set_acc_lo(acc, i, 0x8000); continue
            r = -b
        elif a == 0:
            r = 0
        else:
            r = b
        out[i] = r & 0xFFFF; _set_acc_lo(acc, i, r)
    rsp.vr[vd] = out


def _v_addc(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8; co = 0
    for i in range(8):
        r = s[i] + t[i]
        out[i] = r & 0xFFFF; _set_acc_lo(acc, i, r)
        if r > 0xFFFF: co |= 1 << i
    rsp.vco = co
    rsp.vr[vd] = out


def _v_subc(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8; co = 0
    for i in range(8):
        r = s[i] - t[i]
        out[i] = r & 0xFFFF; _set_acc_lo(acc, i, r)
        if r < 0: co |= 1 << i
        if r != 0: co |= 0x100 << i
    rsp.vco = co
    rsp.vr[vd] = out


def _v_sar(rsp, vd, vs, vt, e):
    acc = rsp.acc
    if e == 8: rsp.vr[vd] = [(a >> 32) & 0xFFFF for a in acc]
    elif e == 9: rsp.vr[vd] = [(a >> 16) & 0xFFFF for a in acc]
    elif e == 10: rsp.vr[vd] = [a & 0xFFFF for a in acc]
    else: rsp.vr[vd] = [0] * 8


def _v_cmp(kind):
    def op(rsp, vd, vs, vt, e):
        s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
        out = [0] * 8; cc = 0
        for i in range(8):
            a = _s16(s[i]); b = _s16(t[i])
            ne = (rsp.vco >> (8 + i)) & 1; c = (rsp.vco >> i) & 1
            if kind == "lt": f = a < b or (a == b and ne and c)
            elif kind == "eq": f = a == b and not ne
            elif kind == "ne": f = a != b or ne
            else: f = a > b or (a == b and not (ne and c))
            if f: cc |= 1 << i
            v = s[i] if f else t[i]
            out[i] = v; _set_acc_lo(acc, i, v)
        rsp.vcc = cc; rsp.vco = 0
        rsp.vr[vd] = out
    return op


def _v_cl(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8
    vcc = rsp.vcc
    for i in range(8):
        a = s[i]; b = t[i]
        carry = (rsp.vco >> i) & 1; ne = (rsp.vco >> (8 + i)) & 1; ce = (rsp.vce >> i) & 1
        le = (vcc >> i) & 1; ge = (vcc >> (8 + i)) & 1
        if carry:
            if not ne:
                ssum = a + b
                lz = (ssum & 0xFFFF) == 0
                ovf = ssum > 0xFFFF
                le = int((lz or not ovf) if ce else (lz and not ovf))
            v = (-b) & 0xFFFF if le else a
        else:
            if not ne:
                ge = int(a - b >= 0)
            v = b if ge else a
        vcc = (vcc & ~((1 << i) | (0x100 << i))) | (le << i) | (ge << (8 + i))
        out[i] = v; _set_acc_lo(acc, i, v)
    rsp.vcc = vcc; rsp.vco = 0; rsp.vce = 0
    rsp.vr[vd] = out


def _v_ch(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8; vcc = 0; vco = 0; vce = 0
    for i in range(8):
        a = _s16(s[i]); b = _s16(t[i])
        if (a ^ b) < 0:
            res = a + b
            v = (-b) & 0xFFFF if res <= 0 else a & 0xFFFF
            le = res <= 0; ge = b < 0
            vco |= 1 << i
            if res != 0 and (a & 0xFFFF) != ((b & 0xFFFF) ^ 0xFFFF): vco |= 0x100 << i
            if res == -1: vce |= 1 << i
        else:
            res = a - b
            v = b & 0xFFFF if res >= 0 else a & 0xFFFF
            le = b < 0; ge = res >= 0
            if res != 0 and (a & 0xFFFF) != ((b & 0xFFFF) ^ 0xFFFF): vco |= 0x100 << i
        if le: vcc |= 1 << i
        if ge: vcc |= 0x100 << i
        out[i] = v; _set_acc_lo(acc, i, v)
    rsp.vcc = vcc; rsp.vco = vco; rsp.vce = vce
    rsp.vr[vd] = out


def _v_cr(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [0] * 8; vcc = 0
    for i in range(8):
        a = _s16(s[i]); b = _s16(t[i])
        if (a ^ b) < 0:
            ge = b < 0; le = a + b + 1 <= 0
            v = (~b) & 0xFFFF if le else a & 0xFFFF
        else:
            le = b < 0; ge = a - b >= 0
            v = b & 0xFFFF if ge else a & 0xFFFF
        if le: vcc |= 1 << i
        if ge: vcc |= 0x100 << i
        out[i] = v; _set_acc_lo(acc, i, v)
    rsp.vcc = vcc; rsp.vco = 0; rsp.vce = 0
    rsp.vr[vd] = out


def _v_mrg(rsp, vd, vs, vt, e):
    s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
    out = [s[i] if (rsp.vcc >> i) & 1 else t[i] for i in range(8)]
    for i in range(8): _set_acc_lo(acc, i, out[i])
    rsp.vco = 0
    rsp.vr[vd] = out


def _v_logic(fn):
    def op(rsp, vd, vs, vt, e):
        s = rsp.vr[vs]; t = rsp.vt_e(vt, e); acc = rsp.acc
        out = [fn(s[i], t[i]) & 0xFFFF for i in range(8)]
        for i in range(8): _set_acc_lo(acc, i, out[i])
        rsp.vr[vd] = out
    return op


def _v_div(kind):
    """VRCP/VRCPL/VRCPH and VRSQ/VRSQL/VRSQH. vd[de] gets the result; accumulator low = vt[e]."""
    def op(rsp, vd, vs, vt, e):
        de = vs & 7
        src = rsp.vt_e(vt, e)
        val = rsp.vr[vt][e & 7]
        if kind in ("rcph", "rsqh"):
            rsp.div_in = (val << 16) & MASK_32
            rsp.div_dp = True
            res = (rsp.div_out >> 16) & 0xFFFF
        else:
            rsq = kind.startswith("rsq")
            if kind in ("rcpl", "rsql") and rsp.div_dp:
                inp = _s32(rsp.div_in | val)
                dp = True
            else:
                inp = _s16(val); dp = False
            rsp.div_out = (_rsp_rsq if rsq else _rsp_rcp)(inp, dp)
            rsp.div_dp = False
            res = rsp.div_out & 0xFFFF
        lanes = list(rsp.vr[vd]); lanes[de] = res; rsp.vr[vd] = lanes
        for i in range(8): _set_acc_lo(rsp.acc, i, src[i])
    return op


def _v_mov(rsp, vd, vs, vt, e):
    src = rsp.vt_e(vt, e)
    de = vs & 7
    lanes = list(rsp.vr[vd]); lanes[de] = src[de]; rsp.vr[vd] = lanes
    for i in range(8): _set_acc_lo(rsp.acc, i, src[i])


def _v_nop(rsp, vd, vs, vt, e):
    pass


_RSP_VOPS = {
    0x00: _v_mulf_special, 0x01: _v_mulu,
    0x04: _v_mul(False, False, "l", False, "l"),   # VMUDL
    0x05: _v_mul(True, False, "m", False, "s"),    # VMUDM
    0x06: _v_mul(False, True, "n", False, "l"),    # VMUDN
    0x07: _v_mul(True, True, "h", False, "s"),     # VMUDH
    0x08: _v_mul(True, True, "f", True, "s"),      # VMACF
    0x09: _v_macu,                                 # VMACU
    0x0C: _v_mul(False, False, "l", True, "l"),    # VMADL
    0x0D: _v_mul(True, False, "m", True, "s"),     # VMADM
    0x0E: _v_mul(False, True, "n", True, "l"),     # VMADN
    0x0F: _v_mul(True, True, "h", True, "s"),      # VMADH
    0x10: _v_addsub(False), 0x11: _v_addsub(True), 0x13: _v_abs, 0x14: _v_addc, 0x15: _v_subc,
    0x1D: _v_sar,
    0x20: _v_cmp("lt"), 0x21: _v_cmp("eq"), 0x22: _v_cmp("ne"), 0x23: _v_cmp("ge"),
    0x24: _v_cl, 0x25: _v_ch, 0x26: _v_cr, 0x27: _v_mrg,
    0x28: _v_logic(lambda a, b: a & b), 0x29: _v_logic(lambda a, b: ~(a & b)),
    0x2A: _v_logic(lambda a, b: a | b), 0x2B: _v_logic(lambda a, b: ~(a | b)),
    0x2C: _v_logic(lambda a, b: a ^ b), 0x2D: _v_logic(lambda a, b: ~(a ^ b)),
    0x30: _v_div("rcp"), 0x31: _v_div("rcpl"), 0x32: _v_div("rcph"), 0x33: _v_mov,
    0x34: _v_div("rsq"), 0x35: _v_div("rsql"), 0x36: _v_div("rsqh"), 0x37: _v_nop, 0x3F: _v_nop,
}


class ACsN64Core:
    def __init__(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.rom = bytearray()
        self.rom_path = ""
        self.rom_header:Optional[N64Header]=None
        self.cic = CIC_NUS_6102
        self.region = REGION_NTSC
        self.ram_mb = 8   # 8 = Expansion Pak installed (DK64, Majora's Mask need it); 4 = stock
        self.pif_ram = bytearray(PIF_RAM_SIZE)
        self.rsp_dmem = bytearray(RSP_DMEM_SIZE)
        self.rsp_imem = bytearray(RSP_IMEM_SIZE)
        self.rsp_pc = 0
        self.audio_signal = False
        self._vi_origin_set = False
        self.save_mgr = SaveManager()
        self.cheat_engine = CheatEngine()
        self.cpu = CPUCore(self)
        self.bus = DeviceBus(self)
        self.ultrahle = UltraHleOs(self)
        self.uh_sym = UltraHleSym(self)
        self.uh_boot_report = ""
        self.running = False
        self.frame_count = 0
        self.vi_counter = 0
        self.cycle_count = 0
        self.vi_clock = 48682
        self.cycles_per_frame = N64_CYCLES_PER_FRAME_NTSC
        self.frame_period = FRAME_PERIOD_NTSC
        self.cycle_limit = INTERP_MAX_STEPS
        self.interp_steps = 40_000
        self.fb_ppm:Optional[bytes]=None
        self.fb_lit = False
        self.boot_turbo = True
        self.last_os_task = 0
        # Harness: fixed instructions per VI frame (deterministic, no wall clock).
        self.fixed_steps: Optional[int] = None
        # kind -> hit count for unimplemented hardware/ucode paths (boot-test report).
        self.unimpl: Dict[str, int] = {}
        # Accurate mode: run the game's own libultra (no OS patches) on a cycle scheduler.
        self.lle = False
        self.now = 0                         # COUNT units since boot (monotonic), as of _count_at_now
        self._count_at_now = 0               # COUNT register value when ``now`` was last synced
        self.events: Dict[str, int] = {}     # kind -> absolute due time (COUNT units)
        self.next_event = 1 << 62
        self.vi_frame_start = 0
        self.ai_fifo: List[Tuple[int, int, int]] = []   # (dram, length, end time) — [0] is playing
        # Battery saves live in save_dir (None = in-memory only, e.g. the headless harness).
        self.save_dir: Optional[str] = os.path.join(_SCRIPT_DIR, "saves")
        self.save_base = ""
        self._save_check_frame = 0
        # Controllers: [buttons, stick x, stick y] per port; port 1 connected by default.
        self.pads = [[0, 0, 0] for _ in range(4)]
        self.pad_connected = [True, False, False, False]
        self.pad_paks = [PAK_NONE] * 4
        self.mempaks = [bytearray(0x8000) for _ in range(4)]
        self.mempak_dirty = [False] * 4
        self.rumble_state = [False] * 4
        self._rumble_probe = [0] * 4
        self.audio_out: List[bytes] = []     # PCM chunks handed to an audio backend
        self.frameskip = normalize_frameskip(os.environ.get("CATHLE_FRAMESKIP", "off"))
        self._fs_reset()
        self._rdp_reset_state()
        self.reset()

    def _save_basename(self) -> str:
        if not self.save_dir or not self.rom_header:
            return ""
        import re
        title = re.sub(r"[^A-Za-z0-9 _.-]+", "", self.rom_header.title or "ROM").strip() or "ROM"
        return os.path.join(self.save_dir, f"{title}-{self.rom_header.crc1:08X}")

    def load_saves(self):
        """Load battery saves + Controller Paks for the current ROM (if a save_dir is set)."""
        self.save_base = self._save_basename()
        if not self.save_base:
            return
        self.save_mgr.load_files(self.save_base)
        for port in range(4):
            try:
                with open(f"{self.save_base}.p{port + 1}.mpk", "rb") as fh:
                    data = fh.read(0x8000)
                self.mempaks[port][:len(data)] = data
            except OSError:
                pass
        self.mempak_dirty = [False] * 4

    def flush_saves(self, force: bool = False) -> bool:
        """Write dirty save media to disk. Returns True if anything was written."""
        if not self.save_base:
            return False
        wrote = False
        try:
            if self.save_mgr.dirty or force:
                wrote |= self.save_mgr.save_files(self.save_base)
            for port in range(4):
                if self.mempak_dirty[port] or (force and self.pad_paks[port] == PAK_MEMPAK):
                    os.makedirs(os.path.dirname(self.save_base), exist_ok=True)
                    with open(f"{self.save_base}.p{port + 1}.mpk", "wb") as fh:
                        fh.write(bytes(self.mempaks[port]))
                    self.mempak_dirty[port] = False
                    wrote = True
        except OSError as e:
            self.note_unimpl(f"save:io:{e.errno}")
        return wrote

    def _maybe_flush_saves(self):
        """Debounce: flush at most once a second of emulated time."""
        if self.frame_count - self._save_check_frame >= 60:
            self._save_check_frame = self.frame_count
            if self.save_mgr.dirty or any(self.mempak_dirty):
                self.flush_saves()

    def set_pad(self, port: int, buttons: int, x: int = 0, y: int = 0):
        """Update a controller: buttons as Joybus bits, stick x/y in -128..127 (±80 typical)."""
        x = max(-128, min(127, int(x))); y = max(-128, min(127, int(y)))
        self.pads[port] = [buttons & 0xFFFF, x, y]
        if port == 0:
            self.ultrahle.cont_pad = buttons & 0xFFFF  # legacy HLE-OS path reads this

    def note_unimpl(self, kind: str):
        self.unimpl[kind] = self.unimpl.get(kind, 0) + 1

    # ── accurate-mode event scheduler (COUNT units) ──
    def sync_time(self) -> int:
        """Exact current time: COUNT advances every instruction, so derive ``now`` from it."""
        c = self.cpu.cp0[CP0_COUNT]
        self.now += (c - self._count_at_now) & MASK_32
        self._count_at_now = c
        return self.now

    def schedule(self, kind: str, delay: int):
        self.events[kind] = self.sync_time() + max(1, int(delay))
        self.next_event = min(self.events.values())

    def cancel_event(self, kind: str):
        if self.events.pop(kind, None) is not None:
            self.next_event = min(self.events.values()) if self.events else 1 << 62

    def vi_frame_len(self) -> int:
        """COUNT units per VI field: CPU/2 ÷ refresh."""
        return N64_COUNT_HZ // (N64_VI_PAL_HZ if self.region == REGION_PAL else N64_VI_NTSC_HZ)

    def vi_current_line(self) -> int:
        vsync = (self.bus.regs.get(VI_V_SYNC, 0) & 0x3FF) or (625 if self.region == REGION_PAL else 525)
        el = self.sync_time() - self.vi_frame_start
        line = (self.bus.regs.get(VI_INTR, 2) & 0x3FF) + (el * vsync) // max(1, self.vi_frame_len())
        line %= vsync
        # Bit 0 is the interlace field; libultra compares half-lines.
        return (line & ~1) | (self.frame_count & 1 if self.bus.regs.get(VI_STATUS, 0) & 0x40 else 0)

    def _ai_duration(self, length: int) -> int:
        dac = (self.bus.regs.get(AI_DACRATE, 0) & 0x3FFF) + 1
        vclock = {REGION_PAL: VI_CLOCK_PAL, REGION_MPAL: VI_CLOCK_MPAL}.get(self.region, VI_CLOCK_NTSC)
        freq = max(1, vclock // dac)
        samples = max(1, length // 4)  # 16-bit stereo
        return max(1, samples * N64_COUNT_HZ // freq)

    def ai_push(self, dram: int, length: int):
        """AI_LEN write: queue a buffer in the 2-deep FIFO; first one starts at once."""
        self.sync_time()
        if length == 0 or len(self.ai_fifo) >= 2:
            return
        dram &= 0xFFFFF8
        if not self.ai_fifo:
            end = self.now + self._ai_duration(length)
            self.ai_fifo.append((dram, length, end))
            self._ai_play(dram, length)
            self.schedule("AI", end - self.now)
        else:
            self.ai_fifo.append((dram, length, 0))
        # A buffer starting (or queuing behind the playing one) raises AI.
        if len(self.ai_fifo) == 1:
            self.bus.hw_interrupts |= MI_INTR_AI

    def _ai_play(self, dram: int, length: int):
        if dram + length <= len(self.rdram):
            self.audio_out.append(bytes(self.rdram[dram:dram + length]))
            if len(self.audio_out) > 64:
                del self.audio_out[:-64]

    def ai_status(self) -> int:
        st = 0
        if self.ai_fifo:
            st |= AI_STATUS_DMA_BUSY | 0x00100000  # busy + enabled
        if len(self.ai_fifo) >= 2:
            st |= AI_STATUS_FIFO_FULL | 0x1
        return st

    def ai_sample_rate(self) -> int:
        dac = (self.bus.regs.get(AI_DACRATE, 0) & 0x3FFF) + 1
        vclock = {REGION_PAL: VI_CLOCK_PAL, REGION_MPAL: VI_CLOCK_MPAL}.get(self.region, VI_CLOCK_NTSC)
        return vclock // dac

    def ai_len_remaining(self) -> int:
        if not self.ai_fifo:
            return 0
        dram, length, end = self.ai_fifo[0]
        total = max(1, self._ai_duration(length))
        left = max(0, end - self.sync_time())
        return (length * left // total) & 0x3FFF8

    def _ev_AI(self):
        if self.ai_fifo:
            self.ai_fifo.pop(0)
        if self.ai_fifo:
            dram, length, _ = self.ai_fifo[0]
            end = self.now + self._ai_duration(length)
            self.ai_fifo[0] = (dram, length, end)
            self._ai_play(dram, length)
            self.schedule("AI", end - self.now)
            self.bus.hw_interrupts |= MI_INTR_AI

    # ── opt-in frame-skip: skip RDP rasterization of whole displayed frames ──
    def _fs_reset(self):
        self._fs_bufs: Dict[int, int] = {}      # colour image addr → bytes per row
        self._fs_display: set = set()            # colour images the VI has scanned out
        self._fs_stale: set = set()              # display buffers whose last frame was skipped
        self._fs_cur = -1                        # colour image of the frame being drawn
        self._fs_skipping = False
        self._fs_since_draw = 0                  # frames skipped since the last drawn one
        self._fs_last_vi = 0.0
        self._fs_vi_dt = 0.0
        self.frames_skipped = 0
        if hasattr(self, "rdp"):
            self.rdp.fs_skip = False

    def _fs_on_cimg(self, addr: int, row_bytes: int):
        """SET_COLOR_IMAGE: a new target starts a new frame; decide whether to rasterize it."""
        if self.frameskip == "off":
            return
        self._fs_bufs[addr] = row_bytes
        if addr not in self._fs_display:
            self.rdp.fs_skip = False   # depth clears / render-to-texture: always drawn, not a frame
            return
        if addr == self._fs_cur:
            self.rdp.fs_skip = self._fs_skipping   # back on the same displayed frame
            return
        self._fs_cur = addr
        if self.frameskip == "auto":
            slow = self._fs_vi_dt > (self.frame_period or FRAME_PERIOD_NTSC) / 0.95
            skip = slow and self._fs_since_draw == 0
        else:
            skip = self._fs_since_draw < int(self.frameskip)
        self._fs_skipping = skip
        self.rdp.fs_skip = skip
        if skip:
            self._fs_since_draw += 1
            self.frames_skipped += 1
            self._fs_stale.add(addr)
        else:
            self._fs_since_draw = 0
            self._fs_stale.discard(addr)

    def _fs_origin_stale(self, origin: int) -> bool:
        """Note which colour image the VI shows; True if that image's latest frame was skipped."""
        best = -1
        for addr, row in self._fs_bufs.items():   # nearest colour image at or below the origin
            if best < addr <= origin < addr + row * 480:
                best = addr
        if best < 0:
            return False
        self._fs_display.add(best)
        return best in self._fs_stale

    def _ev_VI(self):
        if self.frameskip != "off":
            t = time.perf_counter()
            if self._fs_last_vi:
                dt = t - self._fs_last_vi
                self._fs_vi_dt = dt if not self._fs_vi_dt else self._fs_vi_dt * 0.9 + dt * 0.1
            self._fs_last_vi = t
        self._maybe_flush_saves()
        self.bus.hw_interrupts |= MI_INTR_VI
        self.vi_frame_start = self.now
        self.frame_count += 1
        self.render_vi()
        self.cheat_engine.apply(self.bus, self.rdram)
        self.schedule("VI", self.vi_frame_len())
        self._vi_fired = True

    def _ev_SP(self):
        if self.bus.sp_status & SP_STATUS_INTR_BREAK:
            self.bus.hw_interrupts |= MI_INTR_SP

    def _ev_DP(self):
        self.bus.hw_interrupts |= MI_INTR_DP

    def _ev_PI(self):
        self.bus.hw_interrupts |= MI_INTR_PI

    def _ev_SI(self):
        self.bus.hw_interrupts |= MI_INTR_SI

    def _run_events(self):
        self.sync_time()
        while self.events and self.next_event <= self.now:
            kind = min(self.events, key=self.events.get)
            del self.events[kind]
            self.next_event = min(self.events.values()) if self.events else 1 << 62
            getattr(self, "_ev_" + kind)()

    def _advance_idle(self, target: int):
        """Fast-forward an idle loop to ``target`` keeping COUNT/COMPARE consistent."""
        delta = target - self.now
        if delta <= 0:
            return
        cp0 = self.cpu.cp0
        old = cp0[CP0_COUNT]
        cp0[CP0_COUNT] = (old + delta) & MASK_32
        if ((cp0[CP0_COMPARE] - old - 1) & MASK_32) < delta:
            cp0[CP0_CAUSE] |= CAUSE_IP7
        self.now = target
        self._count_at_now = cp0[CP0_COUNT]

    def compare_due_in(self) -> int:
        cp0 = self.cpu.cp0
        return ((cp0[CP0_COMPARE] - cp0[CP0_COUNT]) & MASK_32) or (1 << 32)

    def step_frame_lle(self) -> int:
        """Accurate mode: run until the next VI interrupt fires. Returns instructions run."""
        cpu = self.cpu
        step = cpu.step
        cpo = cpu.count_per_op
        ran = 0
        self._vi_fired = False
        if "VI" not in self.events:
            self.schedule("VI", self.vi_frame_len())
        limit = self.fixed_steps or (1 << 62)
        if self.use_jit:
            return self._frame_jit(limit)
        while not self._vi_fired and ran < limit:
            self.sync_time()
            n = (self.next_event - self.now + cpo - 1) // cpo
            if n > 4096:
                n = 4096
            elif n < 1:
                n = 1
            i = 0
            while i < n:
                step()
                i += 1
                if cpu.idle:
                    cpu.idle = False
                    # Branch-to-self: nothing changes until an interrupt is delivered.
                    st = cpu.cp0[CP0_STATUS]
                    self.sync_time()
                    ran += i
                    i = n = 0
                    wake = self.next_event
                    if (st & STATUS_IE) and not (st & (STATUS_EXL | STATUS_ERL)) and (st & CAUSE_IP7):
                        wake = min(wake, self.now + self.compare_due_in())
                    self._advance_idle(wake)
                    break
            ran += n
            self._run_events()
        self.cycle_count += ran
        return ran

    def _run_blocks(self, budget: int) -> int:
        """Execute compiled blocks for ~budget instructions; returns instructions retired.

        Compiled blocks never write r0 (inline ops skip rd=0, handler fallbacks reset it), so
        only the interpreter path needs the r0 reset — and cpu.step() already does it.
        """
        cpu = self.cpu; cp0 = cpu.cp0; bus = self.bus; g = cpu.gpr
        blocks_get = self.jit.blocks.get; compile_ = self.jit.compile
        cpo = cpu.count_per_op
        M32 = MASK_32; IP2 = CAUSE_IP2; NIP2 = ~CAUSE_IP2; IP7 = CAUSE_IP7
        ran = 0
        while ran < budget:
            # Interrupt delivery between blocks (blocks never straddle a delay slot).
            if bus.hw_interrupts & bus.mi_intr_mask & 0x3F:
                cause = cp0[13] | IP2
            else:
                cause = cp0[13] & NIP2
            cp0[13] = cause
            st = cp0[12]
            if (st & 1) and not (st & 6) and (cause & st & 0xFF00):
                cpu.in_delay = cpu.next_pc != ((cpu.pc + 4) & M32)
                cpu._raise_exception(0, cpu.pc)
            pc = cpu.pc
            if cpu.next_pc == ((pc + 4) & M32):
                fn = blocks_get(pc)
                if fn is None:
                    fn = compile_(pc)
            else:
                fn = None
            if fn is None:
                cpu.step()          # interpreter handles delay-slot state / faults / unimplemented ops
                ran += 1
            else:
                k = fn(cpu, g)
                old = cp0[9]
                dk = k * cpo
                cp0[9] = (old + dk) & M32
                if ((cp0[11] - old - 1) & M32) < dk:
                    cp0[13] |= IP7
                ran += k
            if cpu.idle:
                break
        return ran

    def _frame_jit(self, limit: int) -> int:
        cpu = self.cpu
        cpo = cpu.count_per_op
        ran = 0
        while not self._vi_fired and ran < limit:
            self.sync_time()
            n = (self.next_event - self.now + cpo - 1) // cpo
            n = max(1, min(n, 4096))
            ran += self._run_blocks(n)
            if cpu.idle:
                cpu.idle = False
                st = cpu.cp0[CP0_STATUS]
                self.sync_time()
                wake = self.next_event
                if (st & STATUS_IE) and not (st & (STATUS_EXL | STATUS_ERL)) and (st & CAUSE_IP7):
                    wake = min(wake, self.now + self.compare_due_in())
                self._advance_idle(wake)
            self._run_events()
        self.cycle_count += ran
        return ran

    # ── save states ──
    _STATE_SKIP = {"core", "_tex_cache", "_span_cache", "_span_bound", "fs_skip", "_batch", "_batching", "blocks", "page_blocks", "mapped", "js", "pg", "sd", "stream"}
    _CORE_STATE_FIELDS = ("frame_count", "vi_counter", "cycle_count", "cic", "region", "lle", "now", "_count_at_now",
                          "events", "next_event", "vi_frame_start", "ai_fifo", "pads", "pad_connected", "pad_paks",
                          "mempaks", "rumble_state", "_rumble_probe", "last_os_task", "fb_lit", "rsp_pc",
                          "audio_signal", "_vi_origin_set", "cycles_per_frame", "frame_period", "vi_clock",
                          "_ucode_cache", "ucode_text", "gfx_tasks", "boot_turbo", "interp_steps")

    @classmethod
    def _obj_state(cls, obj) -> Dict[str, Any]:
        """Picklable attribute snapshot of an object (handles __slots__ classes too)."""
        import copy
        if hasattr(obj, "__dict__"):
            items = dict(vars(obj))
        else:
            items = {}
        for klass in type(obj).__mro__:
            for k in getattr(klass, "__slots__", ()):
                if hasattr(obj, k):
                    items[k] = getattr(obj, k)
        components = (ACsN64Core, SoftRDP, GfxHLE, DeviceBus, CPUCore, BlockJIT, AudioHLE,
                      UltraHleOs, UltraHleSym, SaveManager)
        return {k: copy.deepcopy(v) for k, v in items.items()
                if k not in cls._STATE_SKIP and not callable(v) and not k.startswith("__")
                and not isinstance(v, components)}

    def save_state(self) -> bytes:
        """Full machine snapshot (compressed pickle). JIT/texture caches are rebuilt on load."""
        import pickle, zlib, copy
        cpu, bus = self.cpu, self.bus
        st = {
            "version": 1,
            "rom": (self.rom_header.crc1, self.rom_header.crc2) if self.rom_header else (0, 0),
            "cpu": {k: copy.deepcopy(getattr(cpu, k)) for k in
                    ("gpr", "fpr", "cp0", "fcr0", "fcr31", "hi", "lo", "pc", "next_pc", "llbit", "lladdr",
                     "in_delay", "count_per_op", "tlb")},
            "mem": {"rdram": bytes(self.rdram), "dmem": bytes(self.rsp_dmem), "imem": bytes(self.rsp_imem),
                    "pif": bytes(self.pif_ram)},
            "bus": self._obj_state(bus),
            "core": {k: copy.deepcopy(getattr(self, k)) for k in self._CORE_STATE_FIELDS if hasattr(self, k)},
            "save": self._obj_state(self.save_mgr),
            "rdp": self._obj_state(self.rdp), "gfx": self._obj_state(self.gfx), "audio": self._obj_state(self.audio),
            "ultrahle": self._obj_state(self.ultrahle), "uh_sym": self._obj_state(self.uh_sym),
        }
        return zlib.compress(pickle.dumps(st, protocol=pickle.HIGHEST_PROTOCOL), 3)

    def load_state(self, blob: bytes) -> Optional[str]:
        """Restore a snapshot from save_state(). Returns an error string or None."""
        import pickle, zlib
        try:
            st = pickle.loads(zlib.decompress(blob))
        except Exception as e:
            return f"bad state: {e}"
        if st.get("version") != 1:
            return "unsupported state version"
        if self.rom_header and tuple(st["rom"]) != (self.rom_header.crc1, self.rom_header.crc2):
            return "state belongs to a different ROM"
        cpu = self.cpu
        for k, v in st["cpu"].items():
            setattr(cpu, k, v)
        self.rdram[:] = st["mem"]["rdram"]; self.rsp_dmem[:] = st["mem"]["dmem"]
        self.rsp_imem[:] = st["mem"]["imem"]; self.pif_ram[:] = st["mem"]["pif"]
        for obj, key in ((self.bus, "bus"), (self.save_mgr, "save"), (self.rdp, "rdp"), (self.gfx, "gfx"),
                         (self.audio, "audio"), (self.ultrahle, "ultrahle"), (self.uh_sym, "uh_sym")):
            for k, v in st[key].items():
                setattr(obj, k, v)
        for k, v in st["core"].items():
            setattr(self, k, v)
        self.bus.tlb_cache = {}
        self.jit.clear()
        self.rdp._tex_cache.clear(); self.rdp._span_cache.clear()
        self.audio_out = []
        self.render_vi()
        return None

    def hard_reset(self):
        """Power-cycle the loaded cartridge (keeps battery saves); works in both OS modes."""
        self.reset()
        self.bus.regs[PI_STATUS] = 0
        self.bus.hw_interrupts = 0
        if self.lle:
            self.boot_lle()
        self._hle_ipl3_boot()
        self.frame_count = 0

    def boot_lle(self):
        """Switch to accurate mode for the loaded ROM: no OS patches, real interrupts."""
        self.lle = True
        self.bus.strict_tlb = True
        # Counter factor (COUNT ticks per instruction): per-game override from GAME_DB, default 2.
        self.cpu.count_per_op = int(game_info(self.rom).get("cf", 2)) if self.rom else 2
        self.events.clear(); self.next_event = 1 << 62
        self.now = 0
        self._count_at_now = 0
        self.ai_fifo = []
        self.uh_boot_report = ""

    def _rdp_reset_state(self):
        if not hasattr(self, "rdp"):
            self.rdp = SoftRDP(self)
            self.gfx = GfxHLE(self, self.rdp)
            self.audio = AudioHLE(self)
            self.jit = BlockJIT(self)
            self.use_jit = True
            self.rsp = RSP(self)
            self.rsp_mode = "auto"   # auto: HLE known ucodes, LLE RSP otherwise; or force "hle" / "lle"
            self.rsp_busy = False
            self.audio_verify = 0    # audio tasks left to cross-check HLE vs LLE
            self.audio_verify_log: List[Dict[str, Any]] = []
            self.gfx_verify = 0      # graphics tasks left to cross-check HLE vs LLE
            self.gfx_verify_log: List[Dict[str, Any]] = []
            self._ucode_cache: Dict[int, str] = {}
            self.ucode_text: Dict[int, str] = {}
            self.gfx_tasks = 0
        self.rdp.reset()
        self.gfx.reset()
        self.audio.reset()
        self.jit.clear()
        self.rsp.reset()
        self._ucode_cache.clear()

    def reset(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.rsp_dmem = bytearray(RSP_DMEM_SIZE)
        self.rsp_imem = bytearray(RSP_IMEM_SIZE)
        self._vi_origin_set = False
        self.vi_counter = 0
        self.frame_count = 0
        self.fb_ppm = None
        self.fb_lit = False
        self.boot_turbo = True
        self.last_os_task = 0
        self._rdp_reset_state()
        if hasattr(self, "frameskip"):
            self._fs_reset()
        seed_pif_ram(self.pif_ram, self.cic)
        self.cpu.reset()
        self.bus.reset()
        # Persist battery saves across a reset instead of wiping them.
        if getattr(self, "save_base", ""):
            self.flush_saves()
        self.save_mgr.reset()
        if getattr(self, "save_base", ""):
            self.load_saves()
        self.ultrahle.reset()
        self.uh_sym.reset()
        self.uh_boot_report = ""

    def load_rom(self, path, lle: Optional[bool] = None):
        if lle is not None:
            self.lle = lle
        try:
            raw = bytearray(read_rom_file(path))
        except Exception as e:
            return str(e)
        if len(raw) < 0x40:
            return "ROM too small (<64 bytes)"
        norm = normalize_rom_bytes(raw)
        self.rom = bytearray(norm)
        self.rom_path = path
        self.cic, cic_known = identify_cic(self.rom)
        if not cic_known:
            self.note_unimpl("cic:unknown-ipl3")
        self.rom_header = N64Header(self.rom)
        seed_pif_ram(self.pif_ram, self.cic)
        dst = get_rom_region(self.rom)
        self.region = dst
        if dst != REGION_PAL:
            self.vi_clock = 48682
            self.cycles_per_frame = N64_CYCLES_PER_FRAME_NTSC
            self.frame_period = FRAME_PERIOD_NTSC
        else:
            self.vi_clock = 49665
            self.cycles_per_frame = N64_CYCLES_PER_FRAME_PAL
            self.frame_period = FRAME_PERIOD_PAL
        self.cycle_limit = INTERP_MAX_STEPS
        self.interp_steps = INTERP_BOOT_STEPS
        self.fb_lit = False
        self.boot_turbo = True
        self.reset()
        self.bus.regs[PI_STATUS] = 0
        self.bus.hw_interrupts = 0
        if self.lle:
            self.boot_lle()
        self._hle_ipl3_boot()
        self.audio.use_rom_tables(self.rom)
        self.load_saves()
        return None

    def _hle_ipl3_boot(self):
        """Skip real IPL3: seed GPRs like commercial CIC boot, DMA cart→RDRAM, jump to entry.

        Real IPL3 DMAs cartridge bytes from 0x1000 into RDRAM at (boot_address & 0x1FFFFFFF).
        CIC 6103/6106 subtract 0x100000/0x200000 from the header entry before jump+DMA.
        """
        rom = self.rom
        # Cart image at SP DMEM during PIF boot (first 0x1000 bytes = header + IPL3).
        head = rom[:0x1000] if len(rom) >= 0x1000 else rom + bytes(0x1000 - len(rom))
        self.rsp_dmem[:] = bytearray(head[:0x1000])
        if len(self.rsp_imem) >= 0x1000:
            self.rsp_imem[:] = bytearray(head[:0x1000])

        entry = normalize_commercial_entry(
            self.rom_header.boot_address if self.rom_header else 0x80000400
        )
        cic = self.cic
        if cic == CIC_NUS_6103:
            entry = u32(entry - 0x100000)
        elif cic == CIC_NUS_6106:
            entry = u32(entry - 0x200000)
        # UltraHLE boot.c: alternate bootloader (Banjo/F-Zero) clears codebase bits.
        title = ""
        if self.rom_header is not None:
            title = getattr(self.rom_header, "title", "") or ""
        prof = ultrahle_match_ini(title)
        bootloader = int(prof.get("bootloader", 0))
        if len(rom) > 0x544 and be32(rom, 0x540) != 0:
            bootloader = 1
        if bootloader:
            entry = u32(entry & ~0x300000)
        entry_phys = entry & 0x1FFFFFFF
        # Clear RDRAM then perform the IPL3 cart DMA (cart+0x1000 → RDRAM@entry).
        self.rdram[:] = bytearray(RDRAM_SIZE)
        self.jit.clear()
        if len(rom) > 0x1000 and entry_phys < RDRAM_SIZE:
            # IPL3 DMAs exactly 1 MB (cart 0x1000..0x101000); everything else stays zeroed.
            src = memoryview(rom)[0x1000:0x101000]
            n = min(len(src), RDRAM_SIZE - entry_phys)
            self.rdram[entry_phys:entry_phys + n] = src[:n]

        cpu = self.cpu
        g = cpu.gpr
        for i in range(32):
            g[i] = 0
        # Common post-IPL3 register seed (mupen/Project64 HLE-compatible).
        g[1] = 0x0000000000000001
        g[6] = 0xFFFFFFFFA4001F0C
        g[7] = 0xFFFFFFFFA4001F08
        g[8] = 0x00000000000000C0
        g[10] = 0x0000000000000040
        g[11] = 0xFFFFFFFFA4000040
        g[29] = 0xFFFFFFFFA4001FF0
        if cic in (CIC_NUS_6101, CIC_NUS_7102):
            g[22] = 0x000000000000003F
            g[5] = 0xFFFFFFFFC0F1D859
            g[14] = 0x000000002DE108EA
        elif cic == CIC_NUS_6102:
            g[22] = 0x000000000000003F
            g[5] = 0xFFFFFFFFC0F1D859
            g[14] = 0x000000002DE108EA
        elif cic == CIC_NUS_6103:
            g[22] = 0x0000000000000078
            g[5] = 0xFFFFFFFFD4646273
            g[14] = 0x000000001AF53600
        elif cic == CIC_NUS_6105:
            g[22] = 0x0000000000000091
            g[5] = 0xFFFFFFFFDECAAAD1
            g[14] = 0x000000000CF85C13
        elif cic == CIC_NUS_6106:
            g[22] = 0x0000000000000085
            g[5] = 0xFFFFFFFFB04DC903
            g[14] = 0x000000001AF53600
        else:
            g[22] = 0x000000000000003F
        g[22] = CIC_SEEDS.get(cic, g[22])
        # s3=rom type (cart), s4=TV type (0 PAL / 1 NTSC / 2 MPAL), s5=reset type, s7=version.
        region = get_rom_region(rom)
        tv_type = {REGION_PAL: 0, REGION_NTSC: 1, REGION_MPAL: 2}[region]
        g[19] = 0
        g[20] = tv_type
        g[21] = 0
        g[23] = 0x0000000000000000
        g[24] = 0x0000000000000003
        g[31] = 0xFFFFFFFFA4001550
        cpu.hi = 0; cpu.lo = 0
        cpu.llbit = False; cpu.lladdr = 0
        cpu.cp0[CP0_STATUS] = 0x34000000 | STATUS_CU1
        cpu.cp0[CP0_CONFIG] = 0x7006E463
        cpu.cp0[CP0_COUNT] = 0x5000
        cpu.cp0[CP0_CAUSE] = 0x5C
        cpu.cp0[CP0_CONTEXT] = 0x007FFFF0
        cpu.cp0[CP0_EPC] = 0xFFFFFFFF
        cpu.cp0[CP0_BADVADDR] = 0xFFFFFFFF
        cpu.cp0[CP0_ERROREPC] = 0xFFFFFFFF
        cpu.cp0[CP0_COMPARE] = 0xFFFFFFFF
        cpu.cp0[CP0_PRID] = 0x00000B00
        # Low-memory OS globals IPL3 leaves for libultra's osInitialize.
        mem_size = (4 if self.ram_mb == 4 else 8) * 1024 * 1024
        put_be32(self.rdram, 0x300, tv_type)       # osTvType
        put_be32(self.rdram, 0x304, 0)             # osRomType (cartridge)
        put_be32(self.rdram, 0x308, 0xB0000000)    # osRomBase
        put_be32(self.rdram, 0x30C, 0)             # osResetType (cold)
        put_be32(self.rdram, 0x314, 0)             # osVersion
        put_be32(self.rdram, 0x318, mem_size)      # osMemSize
        if cic == CIC_NUS_6105:
            put_be32(self.rdram, 0x3F0, mem_size)  # 6105 IPL3 stores size here
            # 6105 IPL3 leaves a PIF-poll stub in IMEM that the game calls back into.
            for i, w in enumerate((0x3C0DBFC0, 0x8DA807FC, 0x25AD07C0, 0x31080080,
                                   0x5500FFFC, 0x3C0DBFC0, 0x8DA80024, 0x3C0BB000)):
                put_be32(self.rsp_imem, i * 4, w)
        cpu.pc = entry
        cpu.next_pc = u32(entry + 4)
        self.save_mgr.save_type = detect_save_type(rom)
        self.ultrahle.reset()
        self.bus.hw_interrupts = 0
        self.bus.mi_intr_mask = 0
        self.bus.sp_status = SP_STATUS_HALT
        self._vi_origin_set = False
        # UltraHLE boot.c: sym_findfirstos + sym_addpatches after cart DMA.
        if self.lle:
            self.cpu.cp0[CP0_COUNT] = 0
            self._count_at_now = 0
            return
        self.uh_boot_report = self.uh_sym.boot_scan_and_patch(title, entry)
        self.ultrahle.ismario = self.uh_sym.ismario
        self.ultrahle.iszelda = self.uh_sym.iszelda
        self.ultrahle.bootloader = self.uh_sym.bootloader or bootloader


    def trigger_sp_dma(self, to_rsp:bool):
        """SP DMA: len reg = [11:0] length-1, [19:12] count-1, [31:20] RDRAM skip. 8-byte units."""
        reg = self.bus.regs.get(SP_RD_LEN if to_rsp else SP_WR_LEN, 0)
        length = ((reg & 0xFFF) | 7) + 1
        count = ((reg >> 12) & 0xFF) + 1
        skip = (reg >> 20) & 0xFFF
        sp_mem = self.bus.regs.get(SP_MEM_ADDR, 0) & 0x1FF8
        dram = self.bus.regs.get(SP_DRAM_ADDR, 0) & 0x00FFFFF8
        imem = bool(sp_mem & 0x1000)
        mem = self.rsp_imem if imem else self.rsp_dmem
        off = sp_mem & 0xFF8
        rd = self.rdram
        for _ in range(count):
            for k in range(0, length, 8):
                o = (off + k) & 0xFF8
                d = dram + k
                if d + 8 > len(rd):
                    break
                if to_rsp:
                    mem[o:o + 8] = rd[d:d + 8]
                else:
                    rd[d:d + 8] = mem[o:o + 8]
            if not to_rsp:
                self.jit.invalidate_range(dram, length)
            off = (off + length) & 0xFF8
            dram += length + skip
        # Registers advance like hardware so chained DMAs continue where this one ended.
        self.bus.regs[SP_MEM_ADDR] = (sp_mem & 0x1000) | off
        self.bus.regs[SP_DRAM_ADDR] = dram & 0xFFFFF8
        if not self.lle:  # legacy HLE-OS path relied on this; real SP DMA raises nothing
            self.bus.hw_interrupts |= MI_INTR_SP

    def trigger_pi_dma(self):
        """PI DMA — note N64 naming: WR_LEN = cart→RDRAM, RD_LEN = RDRAM→cart."""
        dram = self.bus.regs.get(PI_DRAM_ADDR, 0) & 0x00FFFFFF
        cart = self.bus.regs.get(PI_CART_ADDR, 0) & MASK_32
        rdlen = self.bus.regs.get(PI_RD_LEN, 0) & 0x00FFFFFF
        wrlen = self.bus.regs.get(PI_WR_LEN, 0) & 0x00FFFFFF
        # Hardware: writing PI_WR_LEN starts cart→RDRAM; PI_RD_LEN starts RDRAM→cart.
        cart_to_rdram = wrlen > 0 or rdlen == 0
        length = wrlen if wrlen > 0 else rdlen
        # Register holds length-1; the PI always moves an even number of bytes.
        length = ((length & 0x00FFFFFF) + 2) & ~1
        ca = cart & 0x1FFFFFFF
        # Accept bare cart offsets (UltraHLE / libultra often pass ROM-relative addrs).
        if ca < 0x04000000:
            ca = 0x10000000 + ca
            cart = ca
        if cart_to_rdram:
            if 0x10000000 <= ca < 0x10000000 + len(self.rom):
                off = ca - 0x10000000
                src = self.rom[off:off + length]
            elif 0x08000000 <= ca < 0x09000000:
                self.save_mgr.pi_read(ca, length, self.rdram, dram)
                src = self.rdram[dram:dram + length]
            else:
                src = bytearray(min(length, max(0, RDRAM_SIZE - dram)))
            end = min(dram + len(src), RDRAM_SIZE)
            if end > dram:
                self.rdram[dram:end] = src[: end - dram]
                self.jit.invalidate_range(dram, end - dram)
        else:
            self.save_mgr.pi_write(ca, length, self.rdram, dram)
        self.bus.regs[PI_WR_LEN] = 0
        self.bus.regs[PI_RD_LEN] = 0
        if self.lle:
            self.schedule("PI", length // 8 + 100)  # ~ cart bus throughput
            return
        self.bus.hw_interrupts |= MI_INTR_PI

    def trigger_si_dma(self, read_pif:bool):
        dram = self.bus.regs.get(SI_DRAM_ADDR, 0) & 0x00FFFFFF
        if read_pif:
            self._pif_process_commands()
            for i in range(min(PIF_RAM_SIZE, RDRAM_SIZE - dram)):
                self.rdram[dram + i] = self.pif_ram[i]
        else:
            for i in range(min(PIF_RAM_SIZE, RDRAM_SIZE - dram)):
                self.pif_ram[i] = self.rdram[dram + i]
            if self.lle:
                self._pif_control()  # joybus commands execute when the game reads PIF RAM back
            else:
                self._pif_process_commands()
        if self.lle:
            self.schedule("SI", 0x900)
            return
        self.bus.hw_interrupts |= MI_INTR_SI

    def _pif_control(self):
        """PIF RAM 0x3F control byte: 0x02 = CIC-6105 challenge, 0x08 = terminate boot."""
        pif = self.pif_ram
        ctl = pif[0x3F]
        if ctl & 0x02:
            chl = []
            for i in range(15):
                chl += [(pif[0x30 + i] >> 4) & 0xF, pif[0x30 + i] & 0xF]
            rsp = cic_6105_response(chl[:30])
            pif[0x2E] = pif[0x2F] = 0
            for i in range(15):
                pif[0x30 + i] = (rsp[i * 2] << 4) | rsp[i * 2 + 1]
            pif[0x3F] = 0
            return True
        if ctl & 0x08:
            pif[0x3F] = 0
            return True
        return False

    def _pif_process_commands(self):
        """Joybus: walk PIF RAM command blocks; channels 0-3 = controllers, 4 = cartridge EEPROM."""
        pif = self.pif_ram
        if self._pif_control():
            return
        i = 0
        channel = 0
        while i < PIF_RAM_SIZE - 1:
            b = pif[i]
            if b == 0xFE:          # end of commands
                break
            if b == 0x00:          # skip channel
                channel += 1
                i += 1
                continue
            if b in (0xFF, 0xFD, 0xB4, 0x56, 0xB8):  # padding / reset markers
                i += 1
                continue
            if b & 0xC0:
                break
            tx = b & 0x3F
            if i + 1 >= PIF_RAM_SIZE:
                break
            rx_pos = i + 1
            rx = pif[rx_pos] & 0x3F
            cmd_at = i + 2
            res_at = cmd_at + tx
            if res_at + rx > PIF_RAM_SIZE:
                break
            cmd = bytes(pif[cmd_at:res_at])
            resp = self._joybus(channel, cmd, rx) if tx else None
            if resp is None:
                pif[rx_pos] |= 0x80    # no device / timeout
            else:
                resp = (bytes(resp) + bytes(rx))[:rx]
                pif[res_at:res_at + rx] = resp
            i = res_at + rx
            channel += 1
        pif[0x3F] = 0x00

    def _joybus(self, channel: int, cmd: bytes, rx: int) -> Optional[bytes]:
        """One Joybus transaction. Returns the response bytes or None if nothing answers."""
        op = cmd[0]
        if channel < 4:
            if not self.pad_connected[channel]:
                return None
            pak = self.pad_paks[channel]
            if op in (0x00, 0xFF):                       # info / reset
                return bytes((0x05, 0x00, 0x01 if pak != PAK_NONE else 0x02))
            if op == 0x01:                               # read buttons + stick
                btn, x, y = self.pads[channel]
                return bytes(((btn >> 8) & 0xFF, btn & 0xFF, x & 0xFF, y & 0xFF))
            if op == 0x02 and len(cmd) >= 3:             # pak read 32 bytes
                addr = ((cmd[1] << 8) | cmd[2]) & 0xFFE0
                data = self._pak_read(channel, addr)
                return data + bytes((pak_data_crc(data) if pak != PAK_NONE else 0xFF,))
            if op == 0x03 and len(cmd) >= 35:            # pak write 32 bytes
                addr = ((cmd[1] << 8) | cmd[2]) & 0xFFE0
                data = cmd[3:35]
                self._pak_write(channel, addr, data)
                return bytes((pak_data_crc(data) if pak != PAK_NONE else 0xFF,))
            self.note_unimpl(f"joybus:ctrl:{op:02X}")
            return None
        if channel == 4:
            sm = self.save_mgr
            if not sm.eeprom_present():
                return None
            if op in (0x00, 0xFF):
                return bytes((0x00, 0xC0 if sm.save_type == SAVE_EEPROM_16K else 0x80, 0x00))
            if op == 0x04 and len(cmd) >= 2:             # EEPROM read 8 bytes
                tmp = bytearray(EEPROM_BLOCK)
                sm.eeprom_read_block(cmd[1], tmp)
                return bytes(tmp)
            if op == 0x05 and len(cmd) >= 10:            # EEPROM write 8 bytes
                sm.eeprom_write_block(cmd[1], bytearray(cmd[2:10]))
                return bytes((0x00,))
            if op in (0x06, 0x07, 0x08):                 # RTC status/read/write: no clock on this cart
                return None
            self.note_unimpl(f"joybus:eeprom:{op:02X}")
            return None
        return None

    def _pak_read(self, port: int, addr: int) -> bytes:
        pak = self.pad_paks[port]
        if pak == PAK_MEMPAK:
            if addr < 0x8000:
                return bytes(self.mempaks[port][addr:addr + 32])
            return bytes(32)
        if pak == PAK_RUMBLE:
            if 0x8000 <= addr < 0x9000:
                return bytes((0x80 if self._rumble_probe[port] == 0x80 else 0x00,)) * 32
            return bytes(32)
        return bytes(32)

    def _pak_write(self, port: int, addr: int, data: bytes):
        pak = self.pad_paks[port]
        if pak == PAK_MEMPAK and addr < 0x8000:
            self.mempaks[port][addr:addr + 32] = data
            self.mempak_dirty[port] = True
        elif pak == PAK_RUMBLE:
            if 0x8000 <= addr < 0x9000:
                self._rumble_probe[port] = data[0]
            elif 0xC000 <= addr < 0xD000:
                self.rumble_state[port] = bool(data[0] & 1)

    def process_rsp(self):
        """HLE RSP: complete OSTask, raise SP (and DP for graphics)."""
        if self.lle:
            return self._process_rsp_lle()
        bus = self.bus
        task = u32(getattr(self, "last_os_task", 0))
        task_type = 0
        if task:
            task_type = self.bus.read_u32(task)
            put_be32(self.rsp_dmem, 0xFC0, task_type)
        else:
            task_type = be32(self.rsp_dmem, 0xFC0) if len(self.rsp_dmem) >= 0xFC4 else 0
        bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE
        bus.sp_status &= ~(SP_STATUS_DMA_BUSY | SP_STATUS_DMA_FULL | SP_STATUS_IO_FULL)
        bus.hw_interrupts |= MI_INTR_SP
        # type 1 = graphics, 2 = audio (libultra OSTask)
        if task_type == 1:
            self.process_rdp()
        elif task_type == 2:
            self.process_audio()
        else:
            # Unknown / boot microcode — still retire the task so games continue.
            self.note_unimpl(f"rsp:task{task_type}")
            bus.hw_interrupts |= MI_INTR_DP

    def _run_rsp_lle(self) -> None:
        """Execute the loaded microcode on the LLE RSP until it BREAKs."""
        rsp = self.rsp
        rsp.pc = (self.rsp_pc or 0x04001000) & 0xFFC
        rsp.next_pc = (rsp.pc + 4) & 0xFFC
        self.rsp_busy = True
        try:
            rsp.run()
        finally:
            self.rsp_busy = False
        self.rsp_pc = 0x04001000 | rsp.pc

    def audio_ucode_id(self) -> int:
        import zlib
        u = be32(self.rsp_dmem, 0xFD0) & 0xFFFFFF
        sz = be32(self.rsp_dmem, 0xFD4) or 0x1000
        key = (u, sz)
        uid = self._audio_ids.get(key) if hasattr(self, "_audio_ids") else None
        if uid is None:
            if not hasattr(self, "_audio_ids"):
                self._audio_ids = {}
            uid = zlib.crc32(bytes(self.rdram[u:u + min(sz, 0x1000)])) & MASK_32
            self._audio_ids[key] = uid
        return uid

    def _verify_audio_task(self, uid: int):
        """Run the task on the LLE RSP (kept as truth) and on HLE ABI1; compare SAVEBUFF outputs."""
        self.audio_verify -= 1
        snap_rd = bytes(self.rdram); snap_dm = bytes(self.rsp_dmem)
        self._run_rsp_lle()
        lle_rd = bytes(self.rdram); lle_dm = bytes(self.rsp_dmem); lle_st = self.bus.sp_status
        ev = dict(self.events)
        self.rdram[:] = snap_rd; self.rsp_dmem[:] = snap_dm
        self.audio.saved = []
        try:
            self.audio.run_abi1(be32(snap_dm, 0xFF0) & 0xFFFFFF, be32(snap_dm, 0xFF4))
            err = ""
        except Exception as e:  # garbage alist for a non-ABI1 ucode
            err = f"{type(e).__name__}"
        regions, self.audio.saved = self.audio.saved, None
        worst = 0
        for dst, n in regions:
            for k in range(0, n - 1, 2):
                a = (self.rdram[dst + k] << 8) | self.rdram[dst + k + 1]
                b = (lle_rd[dst + k] << 8) | lle_rd[dst + k + 1]
                worst = max(worst, abs(_s16(a) - _s16(b)))
        self.audio_verify_log.append({"ucode": f"{uid:08X}", "regions": len(regions), "max_diff": worst, "error": err})
        self.rdram[:] = lle_rd; self.rsp_dmem[:] = lle_dm
        self.bus.sp_status = lle_st
        self.events = ev; self.next_event = min(ev.values()) if ev else 1 << 62

    def _verify_gfx_task(self):
        """Render the task on the LLE RSP (kept) and via HLE; compare the color image they wrote."""
        self.gfx_verify -= 1
        snap_rd = bytes(self.rdram); snap_dm = bytes(self.rsp_dmem)
        rdp_state = self._obj_state(self.rdp)
        ev = dict(self.events)
        self._run_rsp_lle()
        cimg, cw, bpp = self.rdp.cimg, self.rdp.cwidth, self.rdp._fb_bpp()
        n = cw * 240 * bpp
        lle_rd = bytes(self.rdram); lle_dm = bytes(self.rsp_dmem); lle_st = self.bus.sp_status
        lle_ev = dict(self.events); lle_rdp = self._obj_state(self.rdp)
        self.rdram[:] = snap_rd; self.rsp_dmem[:] = snap_dm
        for k, v in rdp_state.items(): setattr(self.rdp, k, v)
        self.events = ev; self.next_event = min(ev.values()) if ev else 1 << 62
        try:
            self.process_rdp(data_ptr=be32(snap_dm, 0xFF0) & 0x1FFFFFFF, data_size=be32(snap_dm, 0xFF4),
                             ucode_data=be32(snap_dm, 0xFD8), ucode_data_size=be32(snap_dm, 0xFDC))
            err = ""
        except Exception as e:
            err = type(e).__name__
        a = self.rdram[cimg:cimg + n]; b = lle_rd[cimg:cimg + n]
        # Visible difference: any channel off by more than 2 steps of 5-bit colour (or 16 of 8-bit).
        diff = 0; total = 0; err_sum = 0
        if bpp == 2:
            for k in range(0, min(len(a), len(b)) - 1, 2):
                pa = (a[k] << 8) | a[k + 1]; pb = (b[k] << 8) | b[k + 1]
                d = max(abs(((pa >> sh) & 31) - ((pb >> sh) & 31)) for sh in (11, 6, 1))
                err_sum += d; total += 1
                if d > 2: diff += 1
        else:
            for k in range(0, min(len(a), len(b)) - 3, 4):
                d = max(abs(a[k + c] - b[k + c]) for c in range(3)) >> 3
                err_sum += d; total += 1
                if d > 2: diff += 1
        total = max(1, total)
        fam = detect_gfx_ucode(self.rdram, be32(snap_dm, 0xFD8), be32(snap_dm, 0xFDC))[0] or "unknown"
        self.gfx_verify_log.append({"ucode": fam, "diff_pct": round(100.0 * diff / total, 2),
                                    "mean_err": round(err_sum / total, 3), "error": err})
        self.rdram[:] = lle_rd; self.rsp_dmem[:] = lle_dm; self.bus.sp_status = lle_st
        for k, v in lle_rdp.items(): setattr(self.rdp, k, v)
        self.events = lle_ev; self.next_event = min(lle_ev.values()) if lle_ev else 1 << 62

    def _finish_task(self, task_type: int):
        bus = self.bus
        bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE | SP_STATUS_SIG2_TASKDONE
        bus.sp_status &= ~(SP_STATUS_DMA_BUSY | SP_STATUS_DMA_FULL | SP_STATUS_IO_FULL)
        if "SP" not in self.events:
            self.schedule("SP", 4000 if task_type == 2 else 1000)

    def _process_rsp_lle(self):
        """Accurate mode: OSTask header is in DMEM 0xFC0 (osSpTaskLoad DMAs it there)."""
        bus = self.bus
        task_type = be32(self.rsp_dmem, 0xFC0)
        use_lle = self.rsp_mode == "lle"
        if task_type == 2 and self.rsp_mode == "auto":
            uid = self.audio_ucode_id()
            if self.audio_verify > 0:
                self._verify_audio_task(uid)
                return self._finish_task(2)
            if uid not in AUDIO_HLE_VERIFIED:
                use_lle = True
                self.note_unimpl(f"audio:lle:{uid:08X}")
        if task_type == 1 and self.rsp_mode == "auto" and self.gfx_verify > 0:
            self._verify_gfx_task()
            return self._finish_task(1)
        if task_type == 1 and self.rsp_mode == "auto":
            ud = be32(self.rsp_dmem, 0xFD8) & 0xFFFFFF
            if not detect_gfx_ucode(self.rdram, ud, be32(self.rsp_dmem, 0xFDC))[0]:
                use_lle = True
                self.note_unimpl("rsp:lle-gfx")
        elif task_type not in (1, 2) and self.rsp_mode == "auto":
            use_lle = True
        if use_lle:
            self._run_rsp_lle()
            if not (bus.sp_status & SP_STATUS_HALT):
                self.note_unimpl("rsp:lle-no-break")
                bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE
            return
        try:
            if task_type == 1:
                data_ptr = be32(self.rsp_dmem, 0xFF0)
                data_size = be32(self.rsp_dmem, 0xFF4)
                self.process_rdp(data_ptr=data_ptr & 0x1FFFFFFF, data_size=data_size,
                                 ucode_data=be32(self.rsp_dmem, 0xFD8), ucode_data_size=be32(self.rsp_dmem, 0xFDC))
                self.schedule("DP", 1000)
            elif task_type == 2:
                self.process_audio_task(be32(self.rsp_dmem, 0xFF0), be32(self.rsp_dmem, 0xFF4))
        except TLBException as e:
            # HLE ucode reads RDRAM physically; a bad pointer must never fault the CPU.
            self.note_unimpl(f"rsp:bad-addr:{e.vaddr:08X}")
        if task_type == 1:
            delay = 1000
        elif task_type == 2:
            delay = 4000
        else:
            self.note_unimpl(f"rsp:task{task_type}")
            delay = 1000
        bus.sp_status |= SP_STATUS_HALT | SP_STATUS_BROKE | SP_STATUS_SIG2_TASKDONE
        bus.sp_status &= ~(SP_STATUS_DMA_BUSY | SP_STATUS_DMA_FULL | SP_STATUS_IO_FULL)
        self.schedule("SP", delay)

    def process_audio_task(self, alist: int = 0, size: int = 0):
        """Audio OSTask: run the command list through the HLE audio microcode."""
        self.audio_signal = True
        if alist and size:
            self.audio.run_abi1(alist & 0xFFFFFF, size)

    def gfx_ucode_for_task(self, ucode_data: int, ucode_data_size: int = 0) -> str:
        """Graphics microcode family from the task's ucode data string (cached per address)."""
        key = ucode_data & 0xFFFFFF
        fam = self._ucode_cache.get(key)
        if fam is None:
            fam, text = detect_gfx_ucode(self.rdram, key, ucode_data_size or 0x800)
            if not fam:
                self.note_unimpl(f"gfx:unknown-ucode:{text[:40] or hex(key)}")
                fam = UCODE_F3DEX2 if self.ultrahle.iszelda else UCODE_F3D
            self.ucode_text[key] = text
            self._ucode_cache[key] = fam
        return fam

    def process_rdp(self, data_ptr: int = 0, data_size: int = 0, ucode_data: int = 0, ucode_data_size: int = 0):
        """Graphics OSTask: run the display list through HLE ucode + software RDP."""
        bus = self.bus
        bus.dpc_status &= ~DPC_STATUS_FREEZE
        task = u32(getattr(self, "last_os_task", 0))
        if not data_ptr and task:
            data_ptr = bus.read_u32(task + 0x30)
            ucode_data = bus.read_u32(task + 0x18)
            ucode_data_size = bus.read_u32(task + 0x1C)
        if data_ptr:
            fam = self.gfx_ucode_for_task(ucode_data, ucode_data_size) if ucode_data else (
                UCODE_F3DEX2 if self.ultrahle.iszelda else UCODE_F3D)
            self.gfx.run_task(data_ptr & 0x1FFFFFFF, fam)
            self.gfx_tasks += 1
        if self.lle:
            return  # DP interrupt + VI presentation are scheduled events in accurate mode
        bus.hw_interrupts |= MI_INTR_DP
        if bus.regs.get(VI_ORIGIN, 0):
            self.render_vi()
        elif self.rdp.cimg:
            bus.regs[VI_ORIGIN] = self.rdp.cimg
            self._vi_origin_set = True
            self.render_vi()

    def process_rdp_commands(self, start: int, end: int, xbus: bool = False) -> int:
        """Raw RDP command list (DPC_START..DPC_END) from RDRAM, or DMEM in XBUS mode.

        Returns the address processing stopped at: a command that is not fully inside
        [start, end) waits there (the RDP stalls until DPC_END advances), like hardware.
        """
        if xbus:
            mem, mask = self.rsp_dmem, 0xFF8
        else:
            mem, mask = self.rdram, 0xFFFFF8
        start &= mask; end &= mask
        def w64(a):
            a &= mask
            return (be32(mem, a) << 32) | be32(mem, (a + 4) & (0xFFC if xbus else 0xFFFFFC))
        pc = start
        gfx = self.gfx
        n = (end - start) & mask if xbus else end - start
        stop = start + max(0, n)
        while pc + 8 <= stop:
            w = w64(pc)
            op = (w >> 56) & 0x3F
            if 0x08 <= op <= 0x0F:
                words = 4 + (8 if op & 4 else 0) + (8 if op & 2 else 0) + (2 if op & 1 else 0)
                if pc + words * 8 > stop:
                    break  # incomplete: resume here when more is queued
                self.rdp.raw_triangle([w64(pc + k * 8) for k in range(words)])
                pc += words * 8
                continue
            w0, w1 = (w >> 32) & MASK_32, w & MASK_32
            if op < 0x08:  # NOP and undefined low opcodes
                pc += 8
                continue
            if op in (0x24, 0x25):  # texture rectangle: 128-bit command
                if pc + 16 > stop:
                    break
                w2 = w64(pc + 8)
                h1, h2 = (w2 >> 32) & MASK_32, w2 & MASK_32
                xh = (w0 >> 12) & 0xFFF; yh = w0 & 0xFFF
                tile = (w1 >> 24) & 7; xl = (w1 >> 12) & 0xFFF; yl = w1 & 0xFFF
                sx = lambda v: v - 0x10000 if v & 0x8000 else v
                self.rdp.tex_rect(tile, xl, yl, xh, yh, sx(h1 >> 16), sx(h1 & 0xFFFF), sx(h2 >> 16), sx(h2 & 0xFFFF),
                                  flip=(op == 0x25))
                pc += 16
                continue
            if op == 0x29:  # full sync → DP interrupt
                self.schedule("DP", 50) if self.lle else None
                if not self.lle:
                    self.bus.hw_interrupts |= MI_INTR_DP
                pc += 8
                continue
            saved = gfx.segments
            gfx.segments = [0] * 16  # raw RDP addresses are physical
            gfx.rdp_cmd(op | 0xC0, w0, w1, pc)
            gfx.segments = saved
            pc += 8
        return pc

    def process_audio(self):
        self.audio_signal = True
        self.bus.hw_interrupts |= MI_INTR_AI

    def boot_catch_up(self, max_s: float = 10.0, until_lit: bool = True) -> bool:
        """Burn interpreter time until VI presents (and optionally until lit title GFX).

        Used by the GUI worker so the canvas does not sit on ``VI=1,2,3…`` for minutes.
        """
        if not self.running:
            return False
        self.boot_turbo = True
        self.interp_steps = max(self.interp_steps, INTERP_BOOT_STEPS)
        t0 = time.perf_counter()
        while self.running and (time.perf_counter() - t0) < max_s:
            self.step_frame(budget_s=0.12)
            origin = self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
            if until_lit and self.fb_lit:
                return True
            if (not until_lit) and origin and self.fb_ppm:
                return True
            # Once VI has an origin, keep going a bit for title GFX unless timed out.
            if origin and self.fb_ppm and (time.perf_counter() - t0) > 2.0 and not until_lit:
                return True
        return bool(self.fb_lit or (self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF))

    def vi_geometry(self) -> Optional[Tuple[int, int, int, int]]:
        """(stride, width, height, bpp) of the visible VI image, or None when the VI is blanked."""
        regs = self.bus.regs
        typ = regs.get(VI_STATUS, 0) & 3
        stride = regs.get(VI_WIDTH, 320) & 0xFFF
        if typ < 2 or stride == 0:
            return None
        hs = regs.get(VI_H_START, 0); vs = regs.get(VI_V_START, 0)
        hstart, hend = (hs >> 16) & 0x3FF, hs & 0x3FF
        vstart, vend = (vs >> 16) & 0x3FF, vs & 0x3FF
        if hend <= hstart or vend <= vstart:
            return None  # osViBlack / blanked display
        xs = regs.get(VI_X_SCALE, 0) & 0xFFF; ys = regs.get(VI_Y_SCALE, 0) & 0xFFF
        w = ((hend - hstart) * xs + 1023) >> 10 if xs else stride
        h = ((((vend - vstart) >> 1) * ys) + 1023) >> 10 if ys else 240
        w = max(1, min(w, stride, 640)); h = max(1, min(h, 480))
        return stride, w, h, (4 if typ == 3 else 2)

    def render_vi(self, scale: int = 1):
        origin = self.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
        if self.lle:
            geo = self.vi_geometry()
            if geo is None:
                w, h = 320, 240
                self.fb_ppm = f"P6\n{w} {h}\n255\n".encode("ascii") + bytes(w * h * 3)
                return True
            stride, w, h, bpp = geo
            if self.frameskip != "off" and self._fs_origin_stale(origin) and self.fb_ppm is not None:
                return True
            ppm = vi_frame_to_ppm(self.rdram, origin, stride, w, h, bpp)
            if ppm is not None:
                self.fb_ppm = ppm
                if not self.fb_lit and ppm_brightness(ppm) >= 8.0:
                    self.fb_lit = True
                    self.boot_turbo = False
                return True
            return False
        if origin == 0:
            return False
        width = self.bus.regs.get(VI_WIDTH, 320) & 0xFFF
        if width < 16 or width > 640:
            width = 320
        height = 240
        ppm = rdram_rgb5551_to_ppm(self.rdram, origin, width, height, scale=scale)
        if ppm is not None:
            self.fb_ppm = ppm
            if not self.fb_lit and ppm_brightness(ppm) >= 8.0:
                self.fb_lit = True
                self.boot_turbo = False
            return True
        return False

    def step_frame(self, budget_s: float = INTERP_FRAME_BUDGET_S) -> int:
        """Run one displayed VI frame at N64 60/50 Hz semantics.

        Interprets as many instructions as fit in ``budget_s``, raises VI, advances
        COUNT toward a full N64 frame, and presents the framebuffer. Returns steps run.
        """
        if not self.running:
            return 0
        if self.lle:
            return self.step_frame_lle()
        # CORN-style SM64-first: keep a high instruction budget until the first lit frame.
        fixed = self.fixed_steps
        if self.boot_turbo and not self.fb_lit:
            self.interp_steps = max(self.interp_steps, INTERP_BOOT_STEPS)
            budget_s = max(budget_s, 0.05)
        steps_target = max(INTERP_MIN_STEPS, min(INTERP_MAX_STEPS, int(self.interp_steps)))
        if fixed:
            steps_target = fixed
            budget_s = float("inf")
        t0 = time.perf_counter()
        deadline = t0 + max(0.004, budget_s)
        ran = 0
        cpu = self.cpu
        spin_pc = cpu.pc & ~0x3F
        spin_hits = 0
        # Leave a little time for render_vi inside the same budget.
        cpu_deadline = t0 + max(0.003, budget_s * 0.85)
        while ran < steps_target and self.running:
            cpu.step()
            ran += 1
            pc = cpu.pc
            if (pc & ~0x3F) == spin_pc:
                spin_hits += 1
                if spin_hits >= 24:
                    # Accelerate software delay / decompress / poll loops.
                    cpu.cp0[CP0_COUNT] = u32(cpu.cp0[CP0_COUNT] + 2048)
                    spin_hits = 0
            else:
                spin_pc = pc & ~0x3F
                spin_hits = 0
            if not fixed and (ran & 0xFF) == 0 and time.perf_counter() >= cpu_deadline:
                break
            # Preempt native spin loops when a higher-priority thread is ready
            # (e.g. after VI os_event woke the main thread while idle ran).
            if (ran & 0x1FF) == 0:
                self.ultrahle.maybe_preempt()
            # Fair share: rotate ready game threads so audio/main cannot starve gfx loader.
            if (ran & 0xFF) == 0:
                self.ultrahle.yield_fair()
        self.cycle_count += ran
        catch = max(0, self.cycles_per_frame - ran)
        if catch:
            prev = cpu.cp0[CP0_COUNT]
            cpu.cp0[CP0_COUNT] = u32(prev + catch)
            cmp_ = cpu.cp0[CP0_COMPARE]
            if cmp_ and u32(prev) < cmp_ <= cpu.cp0[CP0_COUNT]:
                cpu.cp0[CP0_CAUSE] |= CAUSE_IP7
        self.frame_count += 1
        vint = self.bus.regs.get(VI_INTR, 0x3FF) & 0x3FF
        self.bus.half_line = vint if vint else 0x200
        self.bus.hw_interrupts |= MI_INTR_VI
        # UltraHLE sync.c: inifile_patches(-1) every frame (e.g. Zelda language byte).
        if self.uh_sym.ini_patches:
            self.uh_sym.apply_ini_patches(-1)
        # UltraHLE sync.c fires RETRACE only. Firing VI+RETRACE doubles messages on
        # the same mq (SM64 audio kick + DMA share a size-1 queue) and drops DMA done.
        self.ultrahle.os_event(OS_EVENT_RETRACE)
        # VI may have woken the game thread — switch to it before the next frame.
        self.ultrahle.maybe_preempt()
        # If still on a low-pri idle/boot thread, force the best ready task.
        self.ultrahle.schedule(0)
        self.ultrahle.tick_time(self.cycles_per_frame)
        self.cheat_engine.apply(self.bus, self.rdram)
        self._maybe_flush_saves()
        # Present real VI framebuffer only — never inject a fake black PPM (that
        # left the GUI stuck on "waiting for VI framebuffer" forever).
        if fixed or time.perf_counter() < deadline or self.fb_ppm is None:
            self.render_vi(scale=1 if (self.fb_lit or fixed) else 2)
        elapsed = max(1e-6, time.perf_counter() - t0)
        # Aim next frame's CPU work at ~75% of the display period (or boot turbo).
        if self.boot_turbo and not self.fb_lit:
            self.interp_steps = INTERP_BOOT_STEPS
        else:
            target = max(0.004, (self.frame_period or FRAME_PERIOD_NTSC) * 0.75)
            rate = ran / elapsed
            self.interp_steps = int(max(INTERP_MIN_STEPS, min(INTERP_MAX_STEPS, rate * target)))
        return ran


# ── Controller input mapping (keyboard + optional pygame gamepad) ──
INPUT_CONFIG_PATH = os.path.join(_SCRIPT_DIR, "cathle_input.json")
UI_CONFIG_PATH = os.path.join(_SCRIPT_DIR, "cathle_ui.json")
STICK_RANGE = 80  # full deflection of a real N64 stick
DEFAULT_KEYMAP = {
    "A": "x", "B": "c", "Z": "z", "START": "Return", "L": "a", "R": "s",
    "CUP": "i", "CDOWN": "k", "CLEFT": "j", "CRIGHT": "l",
    "DUP": "t", "DDOWN": "g", "DLEFT": "f", "DRIGHT": "h",
    "STICK_UP": "Up", "STICK_DOWN": "Down", "STICK_LEFT": "Left", "STICK_RIGHT": "Right",
}
DEFAULT_UI_PREFS = {"show_rom_list": True, "frameskip": "off", "limit_fps": True, "emu_speed": EMU_SPEED_N64}


def load_keymap(path: str = INPUT_CONFIG_PATH) -> Dict[str, str]:
    import json
    km = dict(DEFAULT_KEYMAP)
    try:
        with open(path) as f:
            data = json.load(f)
        km.update({k: str(v) for k, v in data.items() if k in DEFAULT_KEYMAP})
    except (OSError, ValueError):
        pass
    return km


def save_keymap(km: Dict[str, str], path: str = INPUT_CONFIG_PATH):
    import json
    try:
        with open(path, "w") as f:
            json.dump(km, f, indent=1)
    except OSError:
        pass


def load_ui_prefs(path: str = UI_CONFIG_PATH) -> Dict[str, Any]:
    import json
    prefs = dict(DEFAULT_UI_PREFS)
    try:
        with open(path) as f:
            data = json.load(f)
        if isinstance(data, dict):
            if "show_rom_list" in data:
                prefs["show_rom_list"] = bool(data["show_rom_list"])
            if "frameskip" in data:
                prefs["frameskip"] = normalize_frameskip(data["frameskip"])
            if "limit_fps" in data:
                prefs["limit_fps"] = bool(data["limit_fps"])
            if "emu_speed" in data:
                try:
                    prefs["emu_speed"] = max(0.25, min(4.0, float(data["emu_speed"])))
                except (TypeError, ValueError):
                    prefs["emu_speed"] = EMU_SPEED_N64
    except (OSError, ValueError):
        pass
    return prefs


def save_ui_prefs(prefs: Dict[str, Any], path: str = UI_CONFIG_PATH):
    import json
    out = dict(DEFAULT_UI_PREFS)
    out.update(prefs or {})
    try:
        with open(path, "w") as f:
            json.dump(out, f, indent=1)
    except OSError:
        pass


def pad_from_keys(keymap: Dict[str, str], down: set) -> Tuple[int, int, int]:
    """Joybus buttons and stick (x, y) from the set of pressed keysyms (case-insensitive)."""
    low = {k.lower() for k in down}
    pressed = lambda name: keymap.get(name, "").lower() in low
    bits = 0
    for name, bit in PAD_BUTTONS.items():
        if pressed(name):
            bits |= bit
    x = (STICK_RANGE if pressed("STICK_RIGHT") else 0) - (STICK_RANGE if pressed("STICK_LEFT") else 0)
    y = (STICK_RANGE if pressed("STICK_UP") else 0) - (STICK_RANGE if pressed("STICK_DOWN") else 0)
    return bits, x, y


class GamepadInput:
    """Optional pygame joystick → N64 pad (SDL standard layout). Absent pygame = no-op."""
    BUTTONS = {0: "A", 1: "B", 2: "B", 3: "CUP", 4: "L", 5: "R", 6: "Z", 7: "START", 9: "START"}

    def __init__(self):
        self.js = None
        try:
            import pygame  # type: ignore
            pygame.init(); pygame.joystick.init()
            if pygame.joystick.get_count():
                self.js = pygame.joystick.Joystick(0); self.js.init()
            self.pg = pygame
        except Exception:
            self.pg = None

    def poll(self) -> Optional[Tuple[int, int, int]]:
        if not self.js:
            return None
        try:
            self.pg.event.pump()
            bits = 0
            for idx, name in self.BUTTONS.items():
                if idx < self.js.get_numbuttons() and self.js.get_button(idx):
                    bits |= PAD_BUTTONS[name]
            ax = lambda i: self.js.get_axis(i) if i < self.js.get_numaxes() else 0.0
            if ax(2) > 0.5: bits |= PAD_BUTTONS["Z"]
            x = int(ax(0) * STICK_RANGE); y = int(-ax(1) * STICK_RANGE)
            cx, cy = ax(3), ax(4)
            if cx > 0.5: bits |= PAD_BUTTONS["CRIGHT"]
            if cx < -0.5: bits |= PAD_BUTTONS["CLEFT"]
            if cy > 0.5: bits |= PAD_BUTTONS["CDOWN"]
            if cy < -0.5: bits |= PAD_BUTTONS["CUP"]
            return bits, x, y
        except Exception:
            return None


# ── cathle audio engine (live host output) ──
CATHLE_AUDIO_ENGINE = "cathle-audio"
CATHLE_AUDIO_CHANNELS = 2
CATHLE_AUDIO_LATENCY_S = 0.08          # host callback target (≈ 60–100 ms)
CATHLE_AUDIO_RING_S = 0.35             # ring capacity in seconds of stereo PCM
CATHLE_AUDIO_DEFAULT_RATE = 32000


def _be16_stereo_to_f32(data: bytes) -> "Any":
    """Big-endian s16 stereo AI bytes → float32 interleaved [-1, 1] (numpy or array)."""
    n = len(data) & ~1
    if n < 4:
        return _np.zeros(0, dtype=_np.float32) if _np is not None else array.array("f")
    if _np is not None:
        return (_np.frombuffer(data[:n], dtype=">i2").astype(_np.float32) * (1.0 / 32768.0))
    # Pure Python: swap endian + scale with math (no numpy).
    out = array.array("f")
    mv = memoryview(data[:n])
    for i in range(0, n, 2):
        v = (mv[i] << 8) | mv[i + 1]
        if v & 0x8000:
            v -= 0x10000
        out.append(v * (1.0 / 32768.0))
    return out


def _soft_clip_f32(samples, gain: float = 1.0):
    """Soft-clip with math.tanh so loud AI peaks don't hard-distort the host DAC."""
    g = float(gain)
    if _np is not None and isinstance(samples, _np.ndarray):
        x = samples * g
        return _np.tanh(x).astype(_np.float32, copy=False)
    out = array.array("f")
    for s in samples:
        out.append(math.tanh(float(s) * g))
    return out


def _linear_resample_stereo(samples, src_rate: int, dst_rate: int):
    """Math-based linear resample of interleaved stereo float PCM (identity if rates match)."""
    if src_rate <= 0 or dst_rate <= 0 or src_rate == dst_rate:
        return samples
    if _np is not None and isinstance(samples, _np.ndarray):
        n_frames = samples.size // 2
        if n_frames < 2:
            return samples
        dst_frames = max(1, int(round(n_frames * float(dst_rate) / float(src_rate))))
        t = _np.linspace(0.0, n_frames - 1.0, dst_frames, dtype=_np.float64)
        i0 = _np.floor(t).astype(_np.int64)
        i1 = _np.minimum(i0 + 1, n_frames - 1)
        frac = (t - i0).astype(_np.float32)
        left = samples[0::2]; right = samples[1::2]
        l = left[i0] * (1.0 - frac) + left[i1] * frac
        r = right[i0] * (1.0 - frac) + right[i1] * frac
        out = _np.empty(dst_frames * 2, dtype=_np.float32)
        out[0::2] = l; out[1::2] = r
        return out
    # Pure path
    n = len(samples) // 2
    if n < 2:
        return samples
    dst_frames = max(1, int(round(n * float(dst_rate) / float(src_rate))))
    out = array.array("f")
    scale = (n - 1) / max(1, dst_frames - 1)
    for i in range(dst_frames):
        pos = i * scale
        i0 = int(math.floor(pos)); i1 = min(i0 + 1, n - 1)
        f = pos - i0
        l0, r0 = samples[i0 * 2], samples[i0 * 2 + 1]
        l1, r1 = samples[i1 * 2], samples[i1 * 2 + 1]
        out.append(l0 + (l1 - l0) * f)
        out.append(r0 + (r1 - r0) * f)
    return out


def _f32_to_s16le_bytes(samples) -> bytes:
    """Interleaved float32 [-1,1] → little-endian s16 stereo bytes (pygame.mixer Sound)."""
    if _np is not None and isinstance(samples, _np.ndarray):
        clipped = _np.clip(samples, -1.0, 1.0)
        return (clipped * 32767.0).astype("<i2").tobytes()
    out = bytearray()
    for s in samples:
        v = int(max(-1.0, min(1.0, float(s))) * 32767.0)
        out.append(v & 0xFF)
        out.append((v >> 8) & 0xFF)
    return bytes(out)


class CathleAudioEngine:
    """Live cathle host audio engine — callback-driven stereo output for N64 AI DMA.

    Primary backend: **pygame-ce** ``pygame._sdl2.audio.AudioDevice`` (SDL 2.32 /
    Python 3.14). Falls back to ``sounddevice``, then ``pygame.mixer`` Sound
    queue. Uses ``math`` for soft-clip / gain and optional rate convert. With no
    backend every call is a no-op so emulation never depends on host audio.
    """
    ENGINE = CATHLE_AUDIO_ENGINE
    LATENCY_S = CATHLE_AUDIO_LATENCY_S
    RING_S = CATHLE_AUDIO_RING_S

    def __init__(self, volume: float = 1.0, device_rate: int = 0):
        self.stream = None
        self.rate = 0                 # AI / push sample rate
        self.device_rate = int(device_rate) or 0  # 0 = match AI rate
        self.underruns = 0
        self.frames_played = 0
        self.volume = max(0.0, min(2.0, float(volume)))
        self.backend = None           # "pygame-sdl2" | "sounddevice" | "pygame-mixer"
        self._lock = threading.Lock()
        self._ring: Any = None        # float32 interleaved stereo ring
        self._rpos = 0
        self._wpos = 0
        self._count = 0               # samples currently queued
        self._cap = 0
        self._pg = None
        self._sdl_audio = None
        self._sd = None
        self._mixer_ch = None
        self._mixer_rate = 0
        self._probe_backends()

    def _probe_backends(self):
        # Prefer pygame-ce SDL2 AudioDevice (matches Python 3.14.8 + pygame-ce 2.5.x).
        try:
            import pygame  # type: ignore
            from pygame import _sdl2  # type: ignore
            from pygame._sdl2 import audio as sdl_audio  # type: ignore
            _sdl2.init_subsystem(_sdl2.INIT_AUDIO)
            self._pg = pygame
            self._sdl2 = _sdl2
            self._sdl_audio = sdl_audio
            self.backend = "pygame-sdl2"
            return
        except Exception:
            self._pg = self._sdl2 = self._sdl_audio = None
        try:
            import sounddevice  # type: ignore
            self._sd = sounddevice
            self.backend = "sounddevice"
            return
        except Exception:
            self._sd = None
        # Last resort: pygame.mixer Sound queue (no live callback).
        try:
            import pygame  # type: ignore
            self._pg = pygame
            self.backend = "pygame-mixer"
        except Exception:
            self._pg = None
            self.backend = None

    @property
    def available(self) -> bool:
        return self.backend is not None

    @property
    def live(self) -> bool:
        return self.stream is not None or (self.backend == "pygame-mixer" and self._mixer_ch is not None)

    def _ensure_ring(self, rate: int):
        cap = max(CATHLE_AUDIO_CHANNELS * 256, int(rate * self.RING_S) * CATHLE_AUDIO_CHANNELS)
        if self._ring is not None and self._cap == cap:
            return
        if _np is not None:
            self._ring = _np.zeros(cap, dtype=_np.float32)
        else:
            self._ring = array.array("f", [0.0] * cap)
        self._cap = cap
        self._rpos = self._wpos = self._count = 0

    def _ring_write(self, samples) -> int:
        """Append float samples; drop oldest on overflow. Returns samples written."""
        n = len(samples)
        if n <= 0 or self._cap <= 0:
            return 0
        overflow = self._count + n - self._cap
        if overflow > 0:
            drop = overflow + (overflow & 1)  # keep stereo pairs aligned
            self._rpos = (self._rpos + drop) % self._cap
            self._count = max(0, self._count - drop)
        if _np is not None and isinstance(self._ring, _np.ndarray):
            src = _np.asarray(samples, dtype=_np.float32).ravel()
            n = int(src.size)
            first = min(n, self._cap - self._wpos)
            self._ring[self._wpos:self._wpos + first] = src[:first]
            second = n - first
            if second:
                self._ring[0:second] = src[first:first + second]
        else:
            for i, s in enumerate(samples):
                self._ring[(self._wpos + i) % self._cap] = float(s)
        self._wpos = (self._wpos + n) % self._cap
        self._count = min(self._cap, self._count + n)
        return n

    def _ring_read(self, n: int, out) -> int:
        """Fill ``out`` with up to n float samples; pad silence on underrun."""
        got = min(n, self._count)
        if got and _np is not None and isinstance(self._ring, _np.ndarray) and isinstance(out, _np.ndarray):
            first = min(got, self._cap - self._rpos)
            out[:first] = self._ring[self._rpos:self._rpos + first]
            second = got - first
            if second:
                out[first:got] = self._ring[0:second]
            if got < n:
                out[got:n] = 0.0
        elif got:
            for i in range(got):
                out[i] = self._ring[(self._rpos + i) % self._cap]
            for i in range(got, n):
                out[i] = 0.0
        else:
            if _np is not None and isinstance(out, _np.ndarray):
                out[:n] = 0.0
            else:
                for i in range(n):
                    out[i] = 0.0
        self._rpos = (self._rpos + got) % self._cap
        self._count -= got
        if got < n:
            self.underruns += 1
        self.frames_played += got // CATHLE_AUDIO_CHANNELS
        return got

    def _pygame_callback(self, _dev, mem):
        """pygame-ce AudioDevice callback: fill float32 interleaved stereo buffer."""
        mv = memoryview(mem)
        try:
            fmv = mv.cast("f")
        except TypeError:
            return
        n = len(fmv)
        with self._lock:
            if _np is not None:
                buf = _np.empty(n, dtype=_np.float32)
                self._ring_read(n, buf)
                fmv[:] = buf
            else:
                tmp = [0.0] * n
                self._ring_read(n, tmp)
                for i, v in enumerate(tmp):
                    fmv[i] = v

    def _sd_callback(self, outdata, frames, time_info, status):  # noqa: ARG002
        n = frames * CATHLE_AUDIO_CHANNELS
        with self._lock:
            if _np is not None:
                flat = outdata.reshape(-1)
                self._ring_read(n, flat)
            else:
                buf = [0.0] * n
                self._ring_read(n, buf)
                for i, v in enumerate(buf):
                    outdata[i // 2, i % 2] = v

    def _open_pygame_sdl2(self, rate: int):
        play_rate = self.device_rate or rate
        self._ensure_ring(play_rate)
        chunk = max(256, int(play_rate * self.LATENCY_S / 4))
        # AudioDevice(devicename, iscapture, frequency, audioformat, numchannels,
        #             chunksize, allowed_changes, callback)
        fmt = self._sdl_audio.AUDIO_F32LSB
        dev = self._sdl_audio.AudioDevice(
            None, False, play_rate, fmt, CATHLE_AUDIO_CHANNELS, chunk, 0, self._pygame_callback,
        )
        dev.pause(0)  # start streaming
        self.stream = dev
        self.rate = rate
        self.device_rate = int(getattr(dev, "frequency", None) or play_rate)

    def _open_sounddevice(self, rate: int):
        play_rate = self.device_rate or rate
        self._ensure_ring(play_rate)
        block = max(64, int(play_rate * self.LATENCY_S / 4))
        stream = self._sd.OutputStream(
            samplerate=play_rate, channels=CATHLE_AUDIO_CHANNELS, dtype="float32",
            blocksize=block, latency=self.LATENCY_S, callback=self._sd_callback,
        )
        stream.start()
        self.stream = stream
        self.rate = rate
        self.device_rate = play_rate

    def _open_mixer(self, rate: int):
        play_rate = self.device_rate or rate
        try:
            self._pg.mixer.quit()
        except Exception:
            pass
        self._pg.mixer.pre_init(frequency=play_rate, size=-16, channels=2, buffer=1024)
        self._pg.mixer.init(frequency=play_rate, size=-16, channels=2, buffer=1024)
        self._pg.mixer.set_num_channels(8)
        self._mixer_ch = self._pg.mixer.Channel(0)
        self._mixer_rate = play_rate
        self.rate = rate
        self.device_rate = play_rate
        self.stream = self._mixer_ch  # mark live

    def _open_stream(self, rate: int):
        self.close()
        if self.backend == "pygame-sdl2":
            self._open_pygame_sdl2(rate)
        elif self.backend == "sounddevice":
            self._open_sounddevice(rate)
        elif self.backend == "pygame-mixer":
            self._open_mixer(rate)
        else:
            raise RuntimeError("no audio backend")

    def _push_mixer(self, samples):
        """Queue a Sound chunk on the reserved mixer channel (gapless when possible)."""
        raw = _f32_to_s16le_bytes(samples)
        if not raw:
            return
        snd = self._pg.mixer.Sound(buffer=raw)
        ch = self._mixer_ch
        if ch.get_busy():
            ch.queue(snd)
        else:
            ch.play(snd)
        self.frames_played += len(samples) // CATHLE_AUDIO_CHANNELS

    def push(self, chunks: List[bytes], rate: int):
        """Queue AI PCM (big-endian s16 stereo) for live playback at ``rate`` Hz."""
        if not self.backend or not chunks or rate <= 0:
            return
        try:
            if self.stream is None or self.rate != rate:
                self._open_stream(rate)
            data = b"".join(chunks)
            samples = _be16_stereo_to_f32(data)
            play_rate = self.device_rate or rate
            if play_rate != rate:
                samples = _linear_resample_stereo(samples, rate, play_rate)
            samples = _soft_clip_f32(samples, gain=self.volume)
            if self.backend == "pygame-mixer":
                self._push_mixer(samples)
            else:
                with self._lock:
                    self._ring_write(samples)
        except Exception:
            self.close()
            # Demote to next backend so a transient open failure can recover.
            if self.backend == "pygame-sdl2":
                self._sdl_audio = None
                try:
                    import sounddevice  # type: ignore
                    self._sd = sounddevice
                    self.backend = "sounddevice"
                except Exception:
                    self._sd = None
                    if self._pg is not None:
                        self.backend = "pygame-mixer"
                    else:
                        self.backend = None
            elif self.backend == "sounddevice":
                self._sd = None
                self.backend = "pygame-mixer" if self._pg is not None else None
            else:
                self.backend = None

    def set_volume(self, volume: float):
        self.volume = max(0.0, min(2.0, float(volume)))
        if self.backend == "pygame-mixer" and self._mixer_ch is not None:
            try:
                self._mixer_ch.set_volume(min(1.0, self.volume))
            except Exception:
                pass

    def close(self):
        try:
            if self.backend == "pygame-sdl2" and self.stream is not None:
                try:
                    self.stream.pause(1)
                except Exception:
                    pass
                self.stream.close()
            elif self.backend == "sounddevice" and self.stream is not None:
                self.stream.stop(); self.stream.close()
            elif self.backend == "pygame-mixer":
                try:
                    if self._mixer_ch is not None:
                        self._mixer_ch.stop()
                    self._pg.mixer.quit()
                except Exception:
                    pass
        except Exception:
            pass
        self.stream = None
        self._mixer_ch = None
        with self._lock:
            self._rpos = self._wpos = self._count = 0


# Back-compat alias — older call sites / docs referred to AudioOutput.
AudioOutput = CathleAudioEngine


# ── cathle classic Tkinter GUI ──
_COUNTRY_NAMES = {
    0x37: "Beta", 0x41: "NTSC", 0x44: "Germany", 0x45: "USA", 0x46: "France",
    0x49: "Italy", 0x4A: "Japan", 0x50: "Europe", 0x53: "Spain",
    0x55: "Australia", 0x58: "Europe", 0x59: "Europe",
}
_CIC_NAMES = {
    CIC_NUS_6101: "CIC-NUS-6101", CIC_NUS_6102: "CIC-NUS-6102",
    CIC_NUS_6103: "CIC-NUS-6103", CIC_NUS_6105: "CIC-NUS-6105",
    CIC_NUS_6106: "CIC-NUS-6106", CIC_NUS_7102: "CIC-NUS-7102",
    CIC_NUS_8303: "CIC-NUS-8303", CIC_NUS_8401: "CIC-NUS-8401",
    CIC_NUS_DDUS: "CIC-NUS-DDUS", CIC_NUS_5167: "CIC-NUS-5167",
}


def _header_bytes_for_browser(raw):
    data = bytearray(raw[:0x40])
    if len(data) < 0x40:
        return data
    if data[:4] == V64_MAGIC:
        for i in range(0, len(data) - 1, 2):
            data[i], data[i + 1] = data[i + 1], data[i]
    elif data[:4] == N64_LE_MAGIC:
        for i in range(0, len(data) - 3, 4):
            data[i], data[i + 3] = data[i + 3], data[i]
            data[i + 1], data[i + 2] = data[i + 2], data[i + 1]
    return data


_COMPAT_CACHE: Dict[str, Any] = {"mtime": None, "data": {}}


def compat_report_lookup(key: str, path: Optional[str] = None) -> Dict[str, Any]:
    """Row for a ROM (CRC1-CRC2) from compat/report.json next to the script (cached by mtime)."""
    import json
    path = path or os.path.join(_SCRIPT_DIR, "compat", "report.json")
    try:
        mt = os.path.getmtime(path)
    except OSError:
        return {}
    if _COMPAT_CACHE["mtime"] != (path, mt):
        try:
            with open(path) as f:
                _COMPAT_CACHE["data"] = json.load(f)
            _COMPAT_CACHE["mtime"] = (path, mt)
        except (OSError, ValueError):
            return {}
    return _COMPAT_CACHE["data"].get(key, {})


def _format_rom_size(size):
    """Cart size in Mbit (8 MB → 64Mbit)."""
    mbit = max(1, int(round((size * 8) / (1024 * 1024))))
    return f"{mbit}Mbit"


def _format_comments(status: str, core_notes: str = "") -> str:
    """Map boot-test rating to Comments column text."""
    mapping = {
        "Playable": "Playable",
        "In-game": "In-game",
        "Title": "Title Screen",
        "Boots": "Boots",
        "Fails": "* Not Working *",
        "Untested": "?Unknown? - Update or Edit your Ini File!",
    }
    base = mapping.get(status, status or "?Unknown?")
    if status == "Fails" and core_notes:
        return f"* Not Working * ({core_notes})"
    if status == "Playable" and core_notes:
        return f"Playable ({core_notes})"
    return base


class ROMBrowser(tk.Frame if tk else object):
    """cathle ROM list (Name / Country / Size / Filename / Comments)."""

    def __init__(self, parent, on_load, on_info, on_status, directory=None):
        if not tk:
            return
        super().__init__(parent, bg=CATHLE_WIN_GRAY, bd=0)
        self.on_load = on_load
        self.on_info = on_info
        self.on_status = on_status
        self.directory = directory or default_rom_directory()
        self.roms: List[Dict[str, Any]] = []
        self._items: Dict[str, Dict[str, Any]] = {}
        self._sort_column = "good_name"
        self._sort_reverse = False
        self.tree = None
        self.popup = None
        self._build_ui()
        self.scan_roms()

    def _build_ui(self):
        shell = tk.Frame(self, bg=CATHLE_WIN_GRAY, bd=2, relief=tk.SUNKEN)
        shell.pack(fill=tk.BOTH, expand=True, padx=2, pady=(1, 2))
        shell.rowconfigure(0, weight=1)
        shell.columnconfigure(0, weight=1)

        self.tree = ttk.Treeview(shell, columns=[c[0] for c in ROM_BROWSER_COLUMNS],
                                 show="headings", selectmode="browse")
        for key, title, width in ROM_BROWSER_COLUMNS:
            self.tree.heading(key, text=title, anchor=tk.W,
                              command=lambda column=key: self.sort_by(column))
            self.tree.column(key, width=width, minwidth=48, stretch=(key in ("good_name", "comments", "file_name")),
                             anchor=tk.W)
        self.tree.tag_configure("unknown", foreground="#666666")
        self.tree.tag_configure("compatible", foreground="#000000")
        self.tree.tag_configure("playable", foreground="#006600")
        self.tree.tag_configure("ingame", foreground="#007700")
        self.tree.tag_configure("title", foreground="#336600")
        self.tree.tag_configure("boots", foreground="#806000")
        self.tree.tag_configure("fails", foreground="#a00000")
        self.tree.tag_configure("loaded", foreground="#006000")
        ybar = ttk.Scrollbar(shell, orient=tk.VERTICAL, command=self.tree.yview)
        xbar = ttk.Scrollbar(shell, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=ybar.set, xscrollcommand=xbar.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ybar.grid(row=0, column=1, sticky="ns")
        xbar.grid(row=1, column=0, sticky="ew")
        self.tree.bind("<Double-Button-1>", lambda _event: self._load_selected())
        self.tree.bind("<Return>", lambda _event: self._load_selected())
        self.tree.bind("<<TreeviewSelect>>", self._selection_changed)
        self.tree.bind("<Button-3>", self._show_popup)
        self.tree.bind("<Button-2>", self._show_popup)

        self.popup = tk.Menu(self, tearoff=False, font=UI_FONT)
        self.popup.add_command(label="Play Game", command=self._load_selected)
        self.popup.add_separator()
        self.popup.add_command(label="Refresh Rom List", command=self.scan_roms)
        self.popup.add_command(label="Choose Rom Directory...", command=self.choose_directory)
        self.popup.add_separator()
        self.popup.add_command(label="Rom Information", command=self._info_selected)
        self.popup.add_command(label="Game Information", command=self._info_selected)
        self.popup.add_separator()
        self.popup.add_command(label="Edit Game Settings", command=self._info_selected)
        self.popup.add_command(label="Edit Cheats", command=self._load_selected)

    def _read_entry(self, path):
        try:
            size = os.path.getsize(path)
            if size < 0x40:
                return None
            raw = read_rom_file(path, 0x1000)
        except (OSError, ValueError):
            return None
        header_data = _header_bytes_for_browser(raw)
        if len(header_data) < 0x40 or header_data[:4] != Z64_MAGIC:
            return None
        header = N64Header(header_data)
        if header.crc1 == 0 and header.crc2 == 0:
            # Homebrew without a checksum: the core fills it in on load, so key the same way.
            try:
                norm = normalize_rom_bytes(read_rom_file(path, 0x101000))
                header = N64Header(norm)
            except (OSError, ValueError):
                pass
        info = game_info(header_data)
        hdr_title = header.title.strip()
        # Trust the DB name only when the header title agrees (hacks reuse retail cart IDs).
        if info.get("name") and hdr_title and hdr_title.split()[0].casefold() not in info["name"].casefold():
            info = {}
        title = info.get("name") or hdr_title or os.path.splitext(os.path.basename(path))[0]
        country_code = header_data[0x3E]
        cic = get_cic_chip_id(bytes(raw[:0x1000]) if len(raw) >= 0x1000 else header_data)
        # Status comes from the boot-test report (compat/report.json), never guessed.
        row = compat_report_lookup(f"{header.crc1:08X}-{header.crc2:08X}")
        status = row.get("rating", "Untested") if row else "Untested"
        if row and status == "Fails":
            core_notes = row.get("error") or row.get("hang") or next(iter(row.get("unimplemented", {})), "no lit frame")
        elif row:
            core_notes = f"lit @ frame {row.get('first_lit_frame')}" if row.get("first_lit_frame") is not None else ""
        else:
            core_notes = "not boot-tested yet"
        if info.get("ram8"):
            core_notes = (core_notes + "; needs Expansion Pak").lstrip("; ")
        comments = _format_comments(status, core_notes if status in ("Fails", "Playable") else "")
        return {
            "path": path,
            "file_name": os.path.basename(path),
            "internal_name": header.title or "(unknown)",
            "good_name": title,
            "status": status,
            "comments": comments,
            "core_notes": core_notes,
            "plugin_notes": "builtin VI/RDP/RSP HLE",
            "force_feedback": "No",
            "rom_size": _format_rom_size(size),
            "size": size,
            "header": header,
            "country": _COUNTRY_NAMES.get(country_code, f"0x{country_code:02X}"),
            "country_code": country_code,
            "cic": cic,
        }

    def scan_roms(self, directory=None):
        if directory:
            self.directory = directory
        self.roms.clear()
        self._items.clear()
        for item in self.tree.get_children():
            self.tree.delete(item)
        if not os.path.isdir(self.directory):
            self.on_status(f"Rom directory not found: {self.directory}")
            return
        self.on_status(f"Scanning {self.directory}...")
        found = 0
        try:
            for base, dirs, files in os.walk(self.directory):
                dirs[:] = [d for d in dirs if not d.startswith(".")]
                for name in sorted(files, key=str.casefold):
                    if not name.lower().endswith(ROM_EXTENSIONS + (".zip",)):
                        continue
                    entry = self._read_entry(os.path.join(base, name))
                    if entry is None:
                        continue
                    self.roms.append(entry)
                    found += 1
                    if found >= _ROM_SCAN_MAX_FILES:
                        break
                if found >= _ROM_SCAN_MAX_FILES:
                    break
        except OSError as exc:
            self.on_status(f"Rom browser error: {exc}")
        self._populate()
        suffix = " (limit reached)" if found >= _ROM_SCAN_MAX_FILES else ""
        self.on_status(f"{found} Rom{'s' if found != 1 else ''} found{suffix}")

    def _populate(self):
        ordered = sorted(self.roms,
                         key=lambda row: str(row.get(self._sort_column, "")).casefold(),
                         reverse=self._sort_reverse)
        for entry in ordered:
            values = tuple(entry.get(key, "") for key, _title, _width in ROM_BROWSER_COLUMNS)
            tag = {"Playable": "playable", "In-game": "ingame", "Title": "title", "Boots": "boots",
                   "Fails": "fails"}.get(entry.get("status"), "unknown")
            iid = self.tree.insert("", tk.END, values=values, tags=(tag,))
            self._items[iid] = entry

    def sort_by(self, column):
        if self._sort_column == column:
            self._sort_reverse = not self._sort_reverse
        else:
            self._sort_column = column
            self._sort_reverse = False
        for item in self.tree.get_children():
            self.tree.delete(item)
        self._items.clear()
        self._populate()

    def selected_entry(self):
        selection = self.tree.selection()
        return self._items.get(selection[0]) if selection else None

    def choose_directory(self):
        path = filedialog.askdirectory(initialdir=self.directory, title="Choose Rom Directory")
        if path:
            self.scan_roms(path)

    def mark_loaded(self, path):
        target = os.path.normcase(os.path.abspath(path))
        for iid, entry in self._items.items():
            if os.path.normcase(os.path.abspath(entry["path"])) == target:
                self.tree.selection_set(iid)
                self.tree.focus(iid)
                self.tree.see(iid)
                self.tree.item(iid, tags=("loaded",))
                return

    def _selection_changed(self, _event=None):
        entry = self.selected_entry()
        if entry:
            self.on_status(f"{entry['good_name']}  |  {entry['rom_size']}  |  {entry['country']}")

    def _load_selected(self):
        entry = self.selected_entry()
        if entry:
            self.on_load(entry["path"], True)

    def _info_selected(self):
        entry = self.selected_entry()
        if entry:
            self.on_info(entry)

    def _show_popup(self, event):
        row = self.tree.identify_row(event.y)
        if row:
            self.tree.selection_set(row)
            self.tree.focus(row)
            self.popup.tk_popup(event.x_root, event.y_root)


class CathleApp:
    def __init__(self):
        self.core = ACsN64Core()
        self.running = False
        self.loaded_path = ""
        self.recent_roms: List[str] = []
        self.state_slots: Dict[int, Dict[str, Any]] = {}
        self.current_slot = 0
        self._core_lock = threading.RLock()
        self._worker_stop = threading.Event()
        self._worker_wake = threading.Event()
        self._pending_error = ""
        self.emu_thread: Optional[threading.Thread] = None
        self.last_frame_count = 0
        self.fps_time = time.monotonic()
        self.limit_fps = True
        self.emu_speed = DEFAULT_EMU_SPEED  # 1.0 = real N64 (60 VI/s NTSC)
        self.root = None
        self.keys_down: set = set()
        self.keymap = load_keymap()
        self.gamepad: Optional[GamepadInput] = None
        self._pad_state = (0, 0, 0)
        self.audio_out: Optional[CathleAudioEngine] = None
        if tk:
            self._build_gui()

    def _build_gui(self):
        self.root = tk.Tk()
        self.root.title(WINDOW_TITLE)
        self.root.geometry("760x520")
        self.root.minsize(560, 400)
        self.root.configure(bg=CATHLE_WIN_GRAY)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        style = ttk.Style(self.root)
        preferred = "winnative" if platform.system() == "Windows" else "classic"
        if preferred in style.theme_names():
            style.theme_use(preferred)
        style.configure("Treeview", background=CATHLE_PANEL_WHITE, foreground=CATHLE_TEXT,
                        fieldbackground=CATHLE_PANEL_WHITE, font=UI_FONT, rowheight=18,
                        borderwidth=0)
        style.configure("Treeview.Heading", font=UI_FONT, background=CATHLE_WIN_GRAY,
                        foreground=CATHLE_TEXT, relief=tk.RAISED, borderwidth=1)
        style.map("Treeview", background=[("selected", CATHLE_LIST_SEL_BG)],
                  foreground=[("selected", CATHLE_LIST_SEL_FG)])
        style.map("Treeview.Heading", background=[("active", CATHLE_WIN_GRAY)])
        style.configure("TNotebook", background=CATHLE_WIN_GRAY)
        style.configure("TNotebook.Tab", font=UI_FONT, padding=(7, 3))
        style.configure("Vertical.TScrollbar", background=CATHLE_WIN_GRAY,
                        troughcolor=CATHLE_WIN_GRAY, borderwidth=1, arrowsize=14)
        style.configure("Horizontal.TScrollbar", background=CATHLE_WIN_GRAY,
                        troughcolor=CATHLE_WIN_GRAY, borderwidth=1, arrowsize=14)

        self._install_embedded_icon()
        self.status_text = tk.StringVar(value="")
        self.mode_text = tk.StringVar(value="IDLE")
        self.cycle_text = tk.StringVar(value="CYCLE")
        self.cpu_text = tk.StringVar(value="CPU")
        self.gfx_text = tk.StringVar(value="GFX")
        self.snd_text = tk.StringVar(value="SND")
        self.idle_text = tk.StringVar(value="IDLE")
        self.fps_text = tk.StringVar(value="FPS")
        self.start_on_open_var = tk.BooleanVar(value=True)
        ui_prefs = load_ui_prefs()
        self.limit_fps = bool(ui_prefs.get("limit_fps", True))
        self.emu_speed = float(ui_prefs.get("emu_speed", DEFAULT_EMU_SPEED))
        self.limit_fps_var = tk.BooleanVar(value=self.limit_fps)
        self.show_cpu_var = tk.BooleanVar(value=False)
        # Accurate mode runs the game's own libultra (LLE OS); off = cathle HLE OS patches.
        self.accurate_var = tk.BooleanVar(value=True)
        self.always_top_var = tk.BooleanVar(value=False)
        self.fullscreen_var = tk.BooleanVar(value=False)
        self.show_rom_list_var = tk.BooleanVar(value=bool(ui_prefs.get("show_rom_list", True)))
        # Frame skip (opt-in): CATHLE_FRAMESKIP overrides the saved preference.
        self.frameskip_var = tk.StringVar(value=normalize_frameskip(
            os.environ.get("CATHLE_FRAMESKIP", ui_prefs.get("frameskip", "off"))))
        self.core.frameskip = self.frameskip_var.get()
        self.save_slot_var = tk.IntVar(value=0)
        self.rom_directory_var = tk.StringVar(value=default_rom_directory())
        self.menu_items: Dict[str, Tuple[Any, int]] = {}
        self.toolbar_buttons: Dict[str, tk.Button] = {}

        self._build_menus()
        # Classic layout: menus + list + debug + status (no toolbar).

        self._build_status_bar()
        self._build_debug_panel()

        self.content = tk.Frame(self.root, bg=CATHLE_WIN_GRAY)
        self.content.pack(fill=tk.BOTH, expand=True)
        self.browser = ROMBrowser(self.content, self.load_rom, self.show_rom_info,
                                  self._set_status, self.rom_directory_var.get())
        if bool(self.show_rom_list_var.get()):
            self.browser.pack(fill=tk.BOTH, expand=True)
        else:
            self._set_mode("Ready")

        self.emu_view = tk.Frame(self.content, bg="#000000", bd=2, relief=tk.SUNKEN)
        self.canvas = tk.Canvas(self.emu_view, bg="#000000", highlightthickness=0,
                                width=640, height=480)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Configure>", self._center_framebuffer)
        self.canvas_message = self.canvas.create_text(
            320, 220, text="cathle 0.1x\nN64 emulator",
            fill="#b0b0b0", justify=tk.CENTER, font=("Tahoma", 15, "bold"),
            tags=("splash",)
        )
        self._canvas_prompt = "splash"
        if not bool(self.show_rom_list_var.get()):
            self.emu_view.pack(fill=tk.BOTH, expand=True)

        self._bind_shortcuts()
        self._update_actions()
        self.debug_log(DEBUG_BANNER)
        self.root.after(UI_POLL_MS, self._poll)
        self.emu_thread = threading.Thread(target=self._emulation_worker,
                                           name="cathle-r4300i", daemon=True)
        self.emu_thread.start()

    def _install_embedded_icon(self):
        icon = tk.PhotoImage(width=16, height=16)
        icon.put("#202020", to=(1, 1, 15, 15))
        icon.put("#dd2020", to=(2, 2, 8, 8))
        icon.put("#22a044", to=(8, 2, 14, 8))
        icon.put("#2560d8", to=(2, 8, 8, 14))
        icon.put("#e7c51e", to=(8, 8, 14, 14))
        icon.put("#ffffff", to=(6, 4, 10, 12))
        self._app_icon = icon
        try:
            self.root.iconphoto(True, icon)
        except tk.TclError:
            pass

    def _add_menu_command(self, menu, key, label, command, accelerator="", state=tk.NORMAL):
        menu.add_command(label=label, command=command, accelerator=accelerator,
                         state=state, font=UI_FONT)
        self.menu_items[key] = (menu, menu.index(tk.END))

    def _build_menus(self):
        menubar = tk.Menu(self.root, tearoff=False, font=UI_FONT)
        self.root.configure(menu=menubar)

        file_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="File", menu=file_menu)
        self._add_menu_command(file_menu, "open", "Open Rom...", self.open_rom_dialog, "Ctrl+O")
        self._add_menu_command(file_menu, "rom_info", "Rom Information", self.show_loaded_rom_info,
                               "Ctrl+I", tk.DISABLED)
        self._add_menu_command(file_menu, "game_info", "Game Information", self.show_loaded_rom_info,
                               "Ctrl+G", tk.DISABLED)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "start", "Start Emulation", self.start_emulation,
                               "F10", tk.DISABLED)
        self._add_menu_command(file_menu, "end", "End Emulation", self.end_emulation,
                               "F11", tk.DISABLED)
        file_menu.add_separator()
        language_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        language_menu.add_command(label="English", state=tk.DISABLED)
        file_menu.add_cascade(label="Language", menu=language_menu)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "choose_dir", "Choose Rom Directory...",
                               self.choose_rom_directory)
        self._add_menu_command(file_menu, "refresh", "Refresh Rom List",
                               lambda: self.browser.scan_roms(), "F5")
        file_menu.add_separator()
        self.recent_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        self.recent_menu.add_command(label="None Here", state=tk.DISABLED)
        file_menu.add_cascade(label="Recent Rom", menu=self.recent_menu)
        self.recent_dir_menu = tk.Menu(file_menu, tearoff=False, font=UI_FONT)
        self.recent_dir_menu.add_command(label="None Here", state=tk.DISABLED)
        file_menu.add_cascade(label="Recent Rom Directories", menu=self.recent_dir_menu)
        file_menu.add_separator()
        self._add_menu_command(file_menu, "exit", "Exit", self._on_close)

        system_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Emulation", menu=system_menu)
        self._add_menu_command(system_menu, "reset", "Reset", self.reset_core, "F1", tk.DISABLED)
        self._add_menu_command(system_menu, "pause", "Pause", self.pause_emulation, "F2", tk.DISABLED)
        self._add_menu_command(system_menu, "screenshot", "Screenshot Capture",
                               self.capture_screenshot, "F3", tk.DISABLED)
        system_menu.add_separator()
        system_menu.add_checkbutton(label="Limit FPS (N64 speed)", variable=self.limit_fps_var,
                                    accelerator="F4", command=self._sync_options, font=UI_FONT)
        skip_menu = tk.Menu(system_menu, tearoff=False, font=UI_FONT)
        for value, label in (("off", "Off"), ("auto", "Auto (when slow)"), ("1", "Skip 1"), ("2", "Skip 2")):
            skip_menu.add_radiobutton(label=label, value=value, variable=self.frameskip_var,
                                      command=self._set_frameskip, font=UI_FONT)
        system_menu.add_cascade(label="Frame Skip", menu=skip_menu)
        system_menu.add_separator()
        self._add_menu_command(system_menu, "save", "Save", self.save_state, "F5", tk.DISABLED)
        self._add_menu_command(system_menu, "save_as", "Save As...", self.save_state,
                               "Ctrl+S", tk.DISABLED)
        self._add_menu_command(system_menu, "restore", "Restore", self.restore_state,
                               "F7", tk.DISABLED)
        self._add_menu_command(system_menu, "restore_from", "Restore From", self.restore_state,
                               "Ctrl+L", tk.DISABLED)
        system_menu.add_separator()
        slot_menu = tk.Menu(system_menu, tearoff=False, font=UI_FONT)
        slot_menu.add_radiobutton(label="Default", value=0, variable=self.save_slot_var,
                                  command=self._slot_changed, accelerator="0")
        slot_menu.add_separator()
        for slot in range(1, 10):
            slot_menu.add_radiobutton(label=f"Slot {slot}", value=slot,
                                      variable=self.save_slot_var, command=self._slot_changed,
                                      accelerator=str(slot))
        system_menu.add_cascade(label="Current Save State", menu=slot_menu)
        system_menu.add_separator()
        self._add_menu_command(system_menu, "cheats", "Cheats...", self.show_cheats,
                               "Ctrl+C", tk.DISABLED)
        self._add_menu_command(system_menu, "cheat_search", "Cheat Search",
                               self.show_cheats, "Ctrl+R", tk.DISABLED)
        self._add_menu_command(system_menu, "gs_button", "GS Button",
                               lambda: self._set_status("GS Button pressed"), "F9", tk.DISABLED)

        options_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Options", menu=options_menu)
        options_menu.add_checkbutton(label="Full Screen", variable=self.fullscreen_var,
                                     command=self.toggle_fullscreen, accelerator="Alt+Enter",
                                     font=UI_FONT)
        options_menu.add_checkbutton(label="Always On Top", variable=self.always_top_var,
                                     command=self.toggle_always_on_top, accelerator="Ctrl+A",
                                     font=UI_FONT)
        options_menu.add_separator()
        self._add_menu_command(options_menu, "gfx_plugin", "Configure Graphics Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+V")
        self._add_menu_command(options_menu, "audio_plugin", "Configure Audio Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+U")
        self._add_menu_command(options_menu, "control_plugin", "Configure Controller Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+X")
        self._add_menu_command(options_menu, "rsp_plugin", "Configure RSP Plugin...",
                               lambda: self.show_settings("Plugins"), "Ctrl+W")
        options_menu.add_separator()
        options_menu.add_checkbutton(label="Show Rom List", variable=self.show_rom_list_var,
                                     command=self._toggle_rom_list, font=UI_FONT)
        options_menu.add_checkbutton(label="Show CPU usage %", variable=self.show_cpu_var,
                                     font=UI_FONT)
        self._add_menu_command(options_menu, "settings", "Settings...",
                               self.show_settings, "Ctrl+T")

        debugger_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Advanced", menu=debugger_menu)
        self._add_menu_command(debugger_menu, "breakpoint", "Set Breakpoint...",
                               self.set_breakpoint, state=tk.DISABLED)
        debugger_menu.add_separator()
        r4300_menu = tk.Menu(debugger_menu, tearoff=False, font=UI_FONT)
        r4300_menu.add_command(label="R4300i Commands...", command=self.show_registers)
        r4300_menu.add_command(label="R4300i Registers...", command=self.show_registers)
        debugger_menu.add_cascade(label="R4300i", menu=r4300_menu)
        self._add_menu_command(debugger_menu, "memory", "Memory...", self.show_memory,
                               state=tk.DISABLED)
        self._add_menu_command(debugger_menu, "tlb", "TLB Entries...", self.show_tlb,
                               state=tk.DISABLED)
        debugger_menu.add_separator()
        debugger_menu.add_command(label="Call Stack...", state=tk.DISABLED, font=UI_FONT)
        debugger_menu.add_separator()
        logging_menu = tk.Menu(debugger_menu, tearoff=False, font=UI_FONT)
        logging_menu.add_command(label="Log Options", command=lambda: self._set_status("Logging options"))
        logging_menu.add_command(label="Generate Log", command=lambda: self._set_status("Log generated"))
        debugger_menu.add_cascade(label="Logging", menu=logging_menu)

        help_menu = tk.Menu(menubar, tearoff=False, font=UI_FONT)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="Quick Start...", command=lambda: messagebox.showinfo(
            "cathle Quick Start",
            "1. Choose File > Open Rom.\n"
            "2. Select a .z64, .v64, or .n64 image.\n"
            "3. Use Emulation to pause, reset, save, or restore.\n"
            "4. Press Alt+Enter to toggle full screen."
        ), font=UI_FONT)
        help_menu.add_command(label="Keyboard Shortcuts...", command=lambda: messagebox.showinfo(
            "cathle Keyboard Shortcuts",
            "Ctrl+O  Open Rom\n"
            "F1  Reset\nF2  Pause\nF3  Screenshot\n"
            "F5  Refresh or save state\nF7  Restore state\n"
            "F10  Start\nF11  End\nAlt+Enter  Full screen"
        ), font=UI_FONT)
        help_menu.add_separator()
        help_menu.add_command(label="About INI Files", command=lambda: messagebox.showinfo(
            "About cathle", "cathle keeps this edition self-contained; no INI files are required."),
                              font=UI_FONT)
        help_menu.add_command(label="About cathle", command=self.show_about, font=UI_FONT)

    def _build_toolbar(self):
        # Kept for compatibility; classic cathle UI does not show a toolbar.
        self.toolbar = tk.Frame(self.root, bg=CATHLE_WIN_GRAY, bd=1, relief=tk.RAISED)
        self.toolbar_buttons: Dict[str, tk.Button] = {}

        def add_button(key, text, command, width=7):
            button = tk.Button(self.toolbar, text=text, font=UI_FONT, command=command,
                               width=width, padx=2, pady=1, relief=tk.RAISED,
                               bd=1, takefocus=False, bg=CATHLE_BTN_FACE,
                               activebackground=CATHLE_BTN_HIGHLIGHT)
            button.pack(side=tk.LEFT, padx=(2, 0), pady=2)
            self.toolbar_buttons[key] = button

        def separator():
            tk.Frame(self.toolbar, width=2, bg=CATHLE_BTN_SHADOW,
                     bd=1, relief=tk.SUNKEN).pack(side=tk.LEFT, fill=tk.Y, padx=4, pady=3)

        add_button("open", "Open", self.open_rom_dialog)
        add_button("browser", "Roms", lambda: self.show_browser(force=True))
        separator()
        add_button("start", "Start", self.start_emulation)
        add_button("pause", "Pause", self.pause_emulation)
        add_button("reset", "Reset", self.reset_core)
        add_button("end", "End", self.end_emulation)
        separator()
        add_button("screenshot", "Capture", self.capture_screenshot, 8)
        add_button("settings", "Settings", self.show_settings, 8)

    def _build_debug_panel(self):
        """Debug Output strip above the status bar."""
        panel = tk.Frame(self.root, bg=CATHLE_WIN_GRAY, bd=0)
        # Status was packed first with side=BOTTOM; this stacks above it.
        panel.pack(side=tk.BOTTOM, fill=tk.X)
        hdr = tk.Frame(panel, bg=CATHLE_WIN_GRAY)
        hdr.pack(fill=tk.X, padx=2, pady=(2, 0))
        tk.Label(hdr, text="Debug Output", font=UI_FONT, bg=CATHLE_WIN_GRAY,
                 fg=CATHLE_TEXT, anchor=tk.W).pack(side=tk.LEFT)
        body = tk.Frame(panel, bg=CATHLE_WIN_GRAY, bd=2, relief=tk.SUNKEN)
        body.pack(fill=tk.BOTH, expand=True, padx=2, pady=(0, 2))
        self.debug_text = tk.Text(body, height=3, font=UI_FONT_MONO, bg=CATHLE_PANEL_WHITE,
                                  fg=CATHLE_TEXT, relief=tk.FLAT, bd=0, wrap=tk.WORD,
                                  state=tk.DISABLED, highlightthickness=0)
        ybar = tk.Scrollbar(body, orient=tk.VERTICAL, command=self.debug_text.yview,
                            bg=CATHLE_WIN_GRAY, troughcolor=CATHLE_WIN_GRAY, width=14)
        self.debug_text.configure(yscrollcommand=ybar.set)
        self.debug_text.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        ybar.pack(side=tk.RIGHT, fill=tk.Y)

    def debug_log(self, message: str):
        if not getattr(self, "debug_text", None):
            return
        try:
            self.debug_text.configure(state=tk.NORMAL)
            self.debug_text.insert(tk.END, message.rstrip() + "\n")
            self.debug_text.see(tk.END)
            self.debug_text.configure(state=tk.DISABLED)
        except tk.TclError:
            pass

    def _build_status_bar(self):
        """Segmented status: status | CYCLE | CPU | GFX | SND | IDLE | FPS."""
        bar = tk.Frame(self.root, bg=CATHLE_WIN_GRAY, bd=1, relief=tk.RAISED)
        bar.pack(side=tk.BOTTOM, fill=tk.X)
        self.status_bar = bar

        def segment(var, width=None, expand=False, mono=False):
            kwargs = dict(textvariable=var, font=UI_FONT_MONO if mono else UI_FONT,
                          bg=CATHLE_WIN_GRAY, fg=CATHLE_TEXT, anchor=tk.CENTER,
                          relief=tk.SUNKEN, bd=1, padx=4)
            if width is not None:
                kwargs["width"] = width
            lbl = tk.Label(bar, **kwargs)
            lbl.pack(side=tk.LEFT, fill=tk.X if expand else tk.NONE,
                     expand=expand, padx=(1, 0), pady=1)
            return lbl

        segment(self.status_text, expand=True)
        segment(self.cycle_text, width=8, mono=True)
        segment(self.cpu_text, width=6, mono=True)
        segment(self.gfx_text, width=5, mono=True)
        segment(self.snd_text, width=5, mono=True)
        segment(self.idle_text, width=6, mono=True)
        segment(self.fps_text, width=5, mono=True)

    def _bind_shortcuts(self):
        bindings = {
            "<Control-o>": self.open_rom_dialog, "<Control-i>": self.show_loaded_rom_info,
            "<Control-g>": self.show_loaded_rom_info, "<F10>": self.start_emulation,
            "<F11>": self.end_emulation, "<F1>": self.reset_core,
            "<F2>": self.pause_emulation, "<Pause>": self.pause_emulation,
            "<F3>": self.capture_screenshot, "<F4>": self._toggle_limit,
            "<F5>": self._f5_action, "<F7>": self.restore_state,
            "<F9>": lambda: self._set_status("GS Button pressed"),
            "<Control-s>": self.save_state, "<Control-l>": self.restore_state,
            "<Control-c>": self.show_cheats, "<Control-r>": self.show_cheats,
            "<Control-a>": self._toggle_top, "<Control-t>": self.show_settings,
            "<Alt-Return>": self._toggle_fullscreen_key,
        }
        for sequence, callback in bindings.items():
            self.root.bind_all(sequence, lambda event, fn=callback: self._shortcut(fn))
        for slot in range(10):
            self.root.bind_all(str(slot), lambda event, value=slot: self._choose_slot(value))
        # Controller keys: track held keysyms (shortcut sequences above stay more specific).
        self.root.bind_all("<KeyPress>", self._on_key_down, add="+")
        self.root.bind_all("<KeyRelease>", self._on_key_up, add="+")

    def _on_key_down(self, event):
        self.keys_down.add(event.keysym)
        self._update_pad()

    def _on_key_up(self, event):
        self.keys_down.discard(event.keysym)
        self._update_pad()

    def _update_pad(self):
        bits, x, y = pad_from_keys(self.keymap, self.keys_down)
        if self.gamepad is not None:
            gp = self.gamepad.poll()
            if gp:
                bits |= gp[0]
                x = x or gp[1]; y = y or gp[2]
        self._pad_state = (bits, x, y)

    def _shortcut(self, callback):
        callback()
        return "break"

    def _set_status(self, text):
        if self.status_text is not None:
            self.status_text.set(text)

    def _set_mode(self, text: str):
        """Keep mode_text and IDLE status segment in sync."""
        if self.mode_text is not None:
            self.mode_text.set(text)
        if getattr(self, "idle_text", None) is not None:
            label = {
                "Rom Browser": "IDLE",
                "Ready": "IDLE",
                "Loaded": "IDLE",
                "Booting": "BOOT",
                "Running": "RUN",
                "Paused": "PAUSE",
                "Stopped": "STOP",
            }.get(text, (text or "IDLE")[:6].upper())
            self.idle_text.set(label)

    def _set_item_state(self, key, enabled):
        item = self.menu_items.get(key)
        if item:
            item[0].entryconfigure(item[1], state=tk.NORMAL if enabled else tk.DISABLED)

    def _update_actions(self):
        loaded = bool(self.core.rom and self.loaded_path)
        for key in ("rom_info", "game_info", "start", "end", "reset", "pause",
                    "screenshot", "save", "save_as", "restore", "restore_from",
                    "cheats", "cheat_search", "gs_button", "breakpoint", "memory", "tlb"):
            self._set_item_state(key, loaded)
        for key in ("start", "pause", "reset", "end", "screenshot"):
            if key in self.toolbar_buttons:
                self.toolbar_buttons[key].configure(state=tk.NORMAL if loaded else tk.DISABLED)
        if "start" in self.toolbar_buttons:
            self.toolbar_buttons["start"].configure(state=tk.DISABLED if self.running or not loaded else tk.NORMAL)
        if "pause" in self.toolbar_buttons:
            self.toolbar_buttons["pause"].configure(state=tk.NORMAL if self.running else tk.DISABLED)
        self._set_item_state("start", loaded and not self.running)
        self._set_item_state("pause", loaded and self.running)

    def _sync_options(self):
        self.limit_fps = bool(self.limit_fps_var.get())
        self.emu_speed = DEFAULT_EMU_SPEED  # Limit FPS locks to real N64 (1.0×)
        self._persist_ui_prefs()
        if self.limit_fps:
            hz = N64_VI_NTSC_HZ if abs((self.core.frame_period or FRAME_PERIOD_NTSC) - FRAME_PERIOD_NTSC) < 0.001 else N64_VI_PAL_HZ
            self._set_status(f"N64 speed — {hz} VI/s")
        else:
            self._set_status("Speed limiter off (uncapped)")

    def _persist_ui_prefs(self):
        save_ui_prefs({"show_rom_list": bool(self.show_rom_list_var.get()),
                       "frameskip": normalize_frameskip(self.frameskip_var.get()),
                       "limit_fps": bool(self.limit_fps_var.get()),
                       "emu_speed": float(getattr(self, "emu_speed", DEFAULT_EMU_SPEED))})

    def _set_frameskip(self):
        """Frame skip drops RDP rasterization of whole displayed frames; game logic is unchanged."""
        with self._core_lock:
            self.core.frameskip = normalize_frameskip(self.frameskip_var.get())
            self.core._fs_reset()
        self._persist_ui_prefs()

    def _toggle_rom_list(self):
        """Show or hide the ROM browser; preference is saved to cathle_ui.json."""
        self._persist_ui_prefs()
        show = bool(self.show_rom_list_var.get())
        if self.running:
            if not show and self.browser.winfo_ismapped():
                self.show_emulation()
            self._set_status("Rom list shown" if show else "Rom list hidden")
            return
        if show:
            self.show_browser(force=True)
        else:
            self.show_emulation()
            if not self.core.rom:
                self._set_mode("Ready")
        self._set_status("Rom list shown" if show else "Rom list hidden — use File → Open Rom…")

    def _toggle_limit(self):
        self.limit_fps_var.set(not self.limit_fps_var.get())
        self._sync_options()

    def _f5_action(self):
        if self.running:
            self.save_state()
        else:
            self.browser.scan_roms()

    def _toggle_top(self):
        self.always_top_var.set(not self.always_top_var.get())
        self.toggle_always_on_top()

    def _toggle_fullscreen_key(self):
        self.fullscreen_var.set(not self.fullscreen_var.get())
        self.toggle_fullscreen()

    def _choose_slot(self, slot):
        self.save_slot_var.set(slot)
        self._slot_changed()

    def _slot_changed(self):
        self.current_slot = int(self.save_slot_var.get())
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        self._set_status(f"Current save state: {name}")

    def open_rom_dialog(self):
        path = filedialog.askopenfilename(
            title="Open Rom",
            initialdir=self.rom_directory_var.get(),
            filetypes=[("N64 Rom images", "*.z64 *.v64 *.n64 *.rom *.bin"),
                       ("All files", "*.*")]
        )
        if path:
            self.load_rom(path, bool(self.start_on_open_var.get()))

    def choose_rom_directory(self):
        path = filedialog.askdirectory(initialdir=self.rom_directory_var.get(),
                                       title="Choose Rom Directory")
        if path:
            self.rom_directory_var.set(path)
            self.browser.scan_roms(path)
            self._update_recent_directories(path)

    def _update_recent_directories(self, path):
        self.recent_dir_menu.delete(0, tk.END)
        self.recent_dir_menu.add_command(label=path,
                                         command=lambda p=path: self.browser.scan_roms(p))

    def _remember_rom(self, path):
        path = os.path.abspath(path)
        self.recent_roms = [item for item in self.recent_roms
                            if os.path.normcase(item) != os.path.normcase(path)]
        self.recent_roms.insert(0, path)
        del self.recent_roms[10:]
        self.recent_menu.delete(0, tk.END)
        for index, item in enumerate(self.recent_roms, 1):
            self.recent_menu.add_command(
                label=f"{index}. {os.path.basename(item)}",
                command=lambda rom=item: self.load_rom(rom, bool(self.start_on_open_var.get()))
            )

    def load_rom(self, path, auto_start=True):
        self.running = False
        self.core.running = False
        with self._core_lock:
            accurate = bool(self.accurate_var.get()) if hasattr(self, "accurate_var") else True
            err = self.core.load_rom(path, lle=accurate)
        if err:
            messagebox.showerror("Load Error", err)
            self._set_status(f"Error: {err}")
            return
        self.loaded_path = os.path.abspath(path)
        # Target true N64 VI rate (60/50 Hz at emu_speed=1.0); step_frame adapts instruction count.
        self.core.cycle_limit = INTERP_MAX_STEPS
        self.emu_speed = DEFAULT_EMU_SPEED
        self.browser.mark_loaded(path)
        self._remember_rom(path)
        self._update_recent_directories(os.path.dirname(self.loaded_path))
        title = self.core.rom_header.title if self.core.rom_header else os.path.basename(path)
        self.root.title(f"{title} - {WINDOW_TITLE}")
        self._set_status(f"Loaded: {os.path.basename(path)}")
        self.debug_log(f"Loaded ROM: {os.path.basename(path)} ({title})")
        self._set_mode("Loaded")
        self.show_emulation()
        if auto_start:
            self.start_emulation()
        else:
            self._update_actions()

    def start_emulation(self):
        if not self.core.rom or not self.loaded_path:
            self.open_rom_dialog()
            return
        self.show_emulation()
        self.running = True
        self.core.running = True
        self.core.boot_turbo = True
        self.core.fb_lit = False
        self.core.interp_steps = INTERP_BOOT_STEPS
        self._boot_catchup_done = False
        self._display_ppm = None
        self._display_lit = False
        self._display_origin = 0
        self._display_frame = 0
        self._last_blit_bytes = None
        try:
            self.canvas.image = None
            self.canvas.delete("framebuffer")
        except Exception:
            pass
        self._worker_wake.set()
        self._set_mode("Booting")
        self._set_status("Booting…")
        self._set_canvas_prompt("booting", "Booting…")
        self._update_actions()

    def pause_emulation(self):
        if not self.core.rom:
            return
        self.running = False
        self.core.running = False
        self._set_mode("Paused")
        self._set_status("Emulation paused")
        self._set_canvas_prompt("paused")
        self._update_actions()

    def toggle_emu(self):
        self.pause_emulation() if self.running else self.start_emulation()

    def end_emulation(self):
        if not self.core.rom:
            return
        self.running = False
        self.core.running = False
        with self._core_lock:
            self.core.flush_saves()
        self.cycle_text.set("CYCLE")
        self.cpu_text.set("CPU")
        self.gfx_text.set("GFX")
        self.snd_text.set("SND")
        self.fps_text.set("FPS")
        self._set_status("Emulation ended")
        try:
            self.canvas.delete("framebuffer")
            self.canvas.image = None
        except (tk.TclError, AttributeError):
            pass
        self.core.fb_ppm = None
        self._set_canvas_prompt("splash")
        if bool(self.show_rom_list_var.get()):
            self.show_browser(force=True)
        else:
            self.show_emulation()
            self._set_mode("Ready")
        self._update_actions()

    def reset_core(self):
        if not self.core.rom:
            return
        was_running = self.running
        self.running = False
        self.core.running = False
        with self._core_lock:
            # Full power cycle (scheduler, JIT, IPL3) — keeps battery saves.
            self.core.hard_reset()
            self.core.fb_ppm = None
            self.core.fb_lit = False
            self.core.boot_turbo = True
            self.core.interp_steps = INTERP_BOOT_STEPS
            self._boot_catchup_done = False
            self._last_blit_ppm = None
        try:
            self.canvas.delete("framebuffer")
            self.canvas.image = None
        except (tk.TclError, AttributeError):
            pass
        self.running = was_running
        self.core.running = was_running
        if was_running:
            self._worker_wake.set()
            self._set_canvas_prompt("booting")
        self._set_status("System reset")
        self._set_mode("Running" if was_running else "Paused")
        self._update_actions()

    def show_browser(self, force: bool = False):
        if not force and not bool(self.show_rom_list_var.get()):
            self.show_emulation()
            if not self.running and not self.core.rom:
                self._set_mode("Ready")
            return
        self.emu_view.pack_forget()
        if not self.browser.winfo_ismapped():
            self.browser.pack(fill=tk.BOTH, expand=True)
        if not self.running:
            self._set_mode("Rom Browser")

    def show_emulation(self):
        self.browser.pack_forget()
        if not self.emu_view.winfo_ismapped():
            self.emu_view.pack(fill=tk.BOTH, expand=True)
        self._set_canvas_prompt("booting" if self.running or self.core.rom else "splash")

    def _set_canvas_prompt(self, mode: str, detail: str = ""):
        """Idle splash vs boot caption. Hidden once a framebuffer image is on screen."""
        if not self.canvas:
            return
        if getattr(self.canvas, "image", None) is not None and mode != "splash":
            return
        if mode == "booting":
            text = detail or "Booting…\nstarting VI"
        elif mode == "paused":
            text = "Paused"
        else:
            text = "cathle 0.1x\nN64 emulator"
        try:
            self.canvas.delete("splash")
            width = max(320, self.canvas.winfo_width())
            height = max(240, self.canvas.winfo_height())
            self.canvas_message = self.canvas.create_text(
                width // 2, height // 2, text=text,
                fill="#b0b0b0", justify=tk.CENTER, font=("Tahoma", 15, "bold"),
                tags=("splash",)
            )
            self._canvas_prompt = mode
            self._canvas_prompt_detail = detail
        except tk.TclError:
            pass

    def _emulation_worker(self):
        """Drive the core at N64 speed: 60 Hz NTSC / 50 Hz PAL (emu_speed=1.0)."""
        next_frame = time.perf_counter()
        while not self._worker_stop.is_set():
            if not self.running:
                self._worker_wake.wait(0.05)
                self._worker_wake.clear()
                next_frame = time.perf_counter()
                continue
            speed = float(getattr(self, "emu_speed", DEFAULT_EMU_SPEED) or DEFAULT_EMU_SPEED)
            speed = max(0.25, min(4.0, speed))
            base_period = self.core.frame_period or FRAME_PERIOD_NTSC
            period = base_period / speed  # N64 speed → exact VI period
            frame_start = time.perf_counter()
            try:
                boot = self.core.boot_turbo and not self.core.fb_lit
                slices = 12 if boot else 1
                for _ in range(slices):
                    if not self.running or self._worker_stop.is_set():
                        break
                    pcm: List[bytes] = []
                    rate = 0
                    with self._core_lock:
                        self.core.running = self.running
                        self.core.set_pad(0, *self._pad_state)
                        if self.core.audio_out:
                            pcm = list(self.core.audio_out)
                            rate = self.core.ai_sample_rate()
                            self.core.audio_out.clear()
                        if self.core.boot_turbo and not self.core.fb_lit:
                            budget = 0.12
                        elif self.limit_fps:
                            # Leave ~3 ms for present/sleep so wall clock stays at N64 VI rate.
                            budget = max(0.008, period - 0.003)
                        else:
                            budget = min(0.05, period * 2)
                        self.core.step_frame(budget_s=budget)
                        # Publish a lock-free present snapshot for the UI thread.
                        origin = self.core.bus.regs.get(VI_ORIGIN, 0) & 0xFFFFFF
                        if origin and self.core.fb_ppm is None:
                            self.core.render_vi(scale=1)
                        if origin and self.core.fb_ppm:
                            self._display_ppm = bytes(self.core.fb_ppm)
                            self._display_origin = origin
                            self._display_lit = bool(self.core.fb_lit)
                            self._display_frame = self.core.frame_count
                    # Host audio may block on a full device buffer: never while holding the core lock.
                    if pcm:
                        if self.audio_out is None:
                            self.audio_out = CathleAudioEngine()
                        self.audio_out.push(pcm, rate)
                    if self.core.fb_lit:
                        break
            except Exception as exc:
                self._pending_error = f"{type(exc).__name__}: {exc}"
                self.running = False
                self.core.running = False
            if self.limit_fps and self.core.fb_lit:
                next_frame += period
                now = time.perf_counter()
                if now > next_frame + period:
                    next_frame = now  # bank at most one frame of debt: no fast bursts after a stall
                delay = next_frame - now
                if delay > 0.0004:
                    self._worker_stop.wait(delay)
                elif delay < -period:
                    next_frame = now
            else:
                if time.perf_counter() - frame_start < 0.0005:
                    self._worker_stop.wait(0.0)

    def _poll(self):
        if not self.root:
            return
        if self._pending_error:
            error = self._pending_error
            self._pending_error = ""
            self._set_mode("Stopped")
            self._set_status(f"Core stopped: {error}")
            messagebox.showerror("Emulation Error", error)
            self._update_actions()
        if self.emu_view.winfo_ismapped():
            self._blit_framebuffer()
        if self.gamepad is None:
            self.gamepad = GamepadInput()
        if self.gamepad.js is not None:
            self._update_pad()
        now = time.monotonic()
        if now - self.fps_time >= 1.0:
            frames = self.core.frame_count - self.last_frame_count
            self.last_frame_count = self.core.frame_count
            self.fps_time = now
            presents = getattr(self, "_presents", 0)
            shown = presents - getattr(self, "_last_presents", 0)
            self._last_presents = presents
            if self.running:
                target = N64_VI_NTSC_HZ if abs((self.core.frame_period or FRAME_PERIOD_NTSC) - FRAME_PERIOD_NTSC) < 0.001 else N64_VI_PAL_HZ
                cpu_pct = min(100, max(0, frames * 100 // target))
                under = self.audio_out.underruns if self.audio_out is not None else 0
                lost = under - getattr(self, "_last_underruns", 0)
                self._last_underruns = under
                cycles = int(getattr(self.core, "cycle_count", 0) or 0)
                self.cycle_text.set(f"{cycles % 10_000_000}")
                self.cpu_text.set(f"{cpu_pct}%")
                self.gfx_text.set(f"{shown}" if shown else "GFX")
                self.snd_text.set("OK" if lost == 0 else f"×{lost}")
                self.fps_text.set(f"{shown}")
            else:
                self.cycle_text.set("CYCLE")
                self.cpu_text.set("CPU")
                self.gfx_text.set("GFX")
                self.snd_text.set("SND")
                self.fps_text.set("FPS")
        self.root.after(UI_POLL_MS, self._poll)

    def _blit_framebuffer(self):
        """Blit the worker's lock-free display snapshot (no core lock on UI thread)."""
        ppm = getattr(self, "_display_ppm", None)
        origin = getattr(self, "_display_origin", 0)
        lit = getattr(self, "_display_lit", False)
        frame_n = getattr(self, "_display_frame", 0) or self.core.frame_count
        if not ppm or not origin:
            if self.running and not getattr(self.canvas, "image", None):
                now = time.monotonic()
                last = getattr(self, "_boot_prompt_t", 0.0)
                if now - last >= 0.5:
                    self._boot_prompt_t = now
                    self._set_canvas_prompt("booting", "Booting…")
                    self._set_status(f"Booting… ({frame_n})")
            return
        if getattr(self, "_last_blit_bytes", None) == ppm and getattr(self.canvas, "image", None) is not None:
            return
        # One persistent PhotoImage (+ a 2× zoom target) updated in place: no temp file,
        # no new image objects and no canvas item churn per frame.
        image = None
        try:
            src = getattr(self, "_fb_image", None)
            if src is None:
                src = self._fb_image = tk.PhotoImage()
            try:
                src.configure(data=ppm)
            except tk.TclError:  # older Tk: PPM -data must be base64 text
                src.configure(data=base64.b64encode(ppm).decode("ascii"))
            image = src
            if src.width() <= 200:
                zoom = getattr(self, "_fb_zoom", None)
                if zoom is None:
                    zoom = self._fb_zoom = tk.PhotoImage()
                zoom.blank()
                self.root.tk.call(str(zoom), "copy", str(src), "-zoom", 2, 2)
                image = zoom
        except Exception as exc:
            self._set_status(f"Present failed: {exc}")
            image = None
        if image is None:
            return
        try:
            self.canvas.delete("splash")
            if getattr(self.canvas, "image", None) is not image or not self.canvas.find_withtag("framebuffer"):
                self.canvas.delete("framebuffer")
                x = max(0, self.canvas.winfo_width() // 2)
                y = max(0, self.canvas.winfo_height() // 2)
                self.canvas.create_image(x, y, anchor=tk.CENTER, image=image, tags=("framebuffer",))
            self.canvas.image = image
            self._presents = getattr(self, "_presents", 0) + 1
            self._last_blit_bytes = ppm
            self._canvas_prompt = "frame"
            if self.running:
                if lit:
                    self._set_mode("Running")
                    self._set_status("Running")
                else:
                    self._set_mode("Booting")
                    self._set_status(f"VI @ {origin:06X}")
        except tk.TclError:
            pass

    def _center_framebuffer(self, _event=None):
        if getattr(self.canvas, "image", None) is not None:
            try:
                x = max(0, self.canvas.winfo_width() // 2)
                y = max(0, self.canvas.winfo_height() // 2)
                self.canvas.coords("framebuffer", x, y)
            except tk.TclError:
                pass
            return
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())
        try:
            self.canvas.coords(self.canvas_message, width // 2, height // 2)
        except tk.TclError:
            pass

    def _state_path(self, slot: int) -> str:
        h = self.core.rom_header
        tag = f"{h.crc1:08X}-{h.crc2:08X}" if h else "ROM"
        return os.path.join(_SCRIPT_DIR, "states", f"{tag}-{slot}.st")

    def save_state(self):
        if not self.core.rom:
            return
        with self._core_lock:
            blob = self.core.save_state()
        self.state_slots[self.current_slot] = {"blob": blob, "rom_path": self.loaded_path}
        path = self._state_path(self.current_slot)
        try:
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "wb") as fh:
                fh.write(blob)
        except OSError:
            pass
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        self._set_status(f"State saved to {name}")

    def restore_state(self):
        if not self.core.rom:
            return
        blob = None
        state = self.state_slots.get(self.current_slot)
        if state is not None:
            blob = state["blob"]
        else:
            try:
                with open(self._state_path(self.current_slot), "rb") as fh:
                    blob = fh.read()
            except OSError:
                pass
        name = "Default" if self.current_slot == 0 else f"Slot {self.current_slot}"
        if blob is None:
            self._set_status(f"No state stored in {name}")
            return
        with self._core_lock:
            err = self.core.load_state(blob)
        if err:
            messagebox.showwarning("Restore State", err)
            return
        self._set_status(f"State restored from {name}")

    def capture_screenshot(self):
        if not self.core.fb_ppm:
            self._set_status("No framebuffer is available yet")
            return
        path = filedialog.asksaveasfilename(
            title="Screenshot Capture", defaultextension=".ppm",
            initialfile=f"{os.path.splitext(os.path.basename(self.loaded_path))[0]}-capture.ppm",
            filetypes=[("Portable Pixmap", "*.ppm"), ("All files", "*.*")]
        )
        if path:
            try:
                with open(path, "wb") as image_file:
                    image_file.write(self.core.fb_ppm)
                self._set_status(f"Screenshot saved: {os.path.basename(path)}")
            except OSError as exc:
                messagebox.showerror("Screenshot Capture", str(exc))

    def toggle_fullscreen(self):
        try:
            self.root.attributes("-fullscreen", bool(self.fullscreen_var.get()))
        except tk.TclError:
            pass

    def toggle_always_on_top(self):
        try:
            self.root.attributes("-topmost", bool(self.always_top_var.get()))
        except tk.TclError:
            pass

    def _browser_entry_for_loaded(self):
        target = os.path.normcase(os.path.abspath(self.loaded_path)) if self.loaded_path else ""
        for entry in self.browser.roms:
            if os.path.normcase(os.path.abspath(entry["path"])) == target:
                return entry
        if self.core.rom_header and self.loaded_path:
            header = self.core.rom_header
            return {
                "path": self.loaded_path, "file_name": os.path.basename(self.loaded_path),
                "good_name": header.title or os.path.basename(self.loaded_path),
                "internal_name": header.title or "(unknown)", "header": header,
                "size": len(self.core.rom), "rom_size": _format_rom_size(len(self.core.rom)),
                "country_code": self.core.rom[0x3E] if len(self.core.rom) > 0x3E else 0,
                "country": _COUNTRY_NAMES.get(self.core.rom[0x3E], "Unknown") if len(self.core.rom) > 0x3E else "Unknown",
                "cic": self.core.cic,
            }
        return None

    def show_loaded_rom_info(self):
        entry = self._browser_entry_for_loaded()
        if entry:
            self.show_rom_info(entry)

    def show_rom_info(self, entry):
        header = entry["header"]
        dialog = tk.Toplevel(self.root)
        dialog.title("Rom Information")
        dialog.configure(bg=CATHLE_WIN_GRAY)
        dialog.resizable(False, False)
        dialog.transient(self.root)
        fields = [
            ("ROM Name:", entry.get("internal_name", "")),
            ("File Name:", entry.get("file_name", "")),
            ("Location:", os.path.dirname(entry.get("path", ""))),
            ("Rom Size:", entry.get("rom_size", _format_rom_size(entry.get("size", 0)))),
            ("Cartridge ID:", header.cart_id),
            ("Release Version:", f"0x{header.release:08X}"),
            ("Clock Rate:", f"0x{header.clock_rate:08X}"),
            ("Country:", entry.get("country", "Unknown")),
            ("CRC1:", f"{header.crc1:08X}"),
            ("CRC2:", f"{header.crc2:08X}"),
            ("CIC Chip:", _CIC_NAMES.get(entry.get("cic"), "Unknown")),
        ]
        group = tk.LabelFrame(dialog, text="", bg=CATHLE_WIN_GRAY, font=UI_FONT)
        group.pack(fill=tk.BOTH, expand=True, padx=8, pady=(7, 3))
        for row, (label, value) in enumerate(fields):
            tk.Label(group, text=label, bg=CATHLE_WIN_GRAY, font=UI_FONT,
                     anchor=tk.W, width=17).grid(row=row, column=0, sticky="w", padx=(5, 2), pady=2)
            box = tk.Entry(group, font=UI_FONT, relief=tk.SUNKEN, bd=1, width=48)
            box.insert(0, value)
            box.configure(state="readonly", readonlybackground="#ffffff")
            box.grid(row=row, column=1, sticky="ew", padx=(2, 5), pady=2)
        tk.Button(dialog, text="Close", width=12, font=UI_FONT,
                  command=dialog.destroy).pack(side=tk.RIGHT, padx=9, pady=(2, 8))

    def show_settings(self, initial_tab="Options"):
        dialog = tk.Toplevel(self.root)
        dialog.title("Settings")
        dialog.geometry("525x365")
        dialog.minsize(500, 340)
        dialog.configure(bg=CATHLE_WIN_GRAY)
        dialog.transient(self.root)
        notebook = ttk.Notebook(dialog)
        notebook.pack(fill=tk.BOTH, expand=True, padx=7, pady=7)
        tabs = {}
        for name in ("Options", "Directories", "Plugins", "Input"):
            tab = tk.Frame(notebook, bg=CATHLE_WIN_GRAY)
            notebook.add(tab, text=name)
            tabs[name] = tab
        if initial_tab in tabs:
            notebook.select(tabs[initial_tab])

        options = tabs["Options"]
        core_box = tk.LabelFrame(options, text=" Core Defaults ", bg=CATHLE_WIN_GRAY, font=UI_FONT)
        core_box.pack(fill=tk.X, padx=9, pady=9)
        tk.Label(core_box, text="CPU core style:", bg=CATHLE_WIN_GRAY,
                 font=UI_FONT).grid(row=0, column=0, sticky="w", padx=8, pady=7)
        ttk.Combobox(core_box, values=("Interpreter", "Cached Interpreter"),
                     state="readonly", width=25).grid(row=0, column=1, padx=8, pady=7)
        tk.Checkbutton(options, text="Start Emulation when rom is opened?",
                       variable=self.start_on_open_var, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Show Rom List", variable=self.show_rom_list_var,
                       command=self._toggle_rom_list, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Limit FPS (N64 speed — 60 VI/s NTSC)", variable=self.limit_fps_var,
                       command=self._sync_options, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Show CPU usage %", variable=self.show_cpu_var,
                       bg=CATHLE_WIN_GRAY, font=UI_FONT).pack(anchor="w", padx=13, pady=3)
        tk.Checkbutton(options, text="Accurate mode (run the game's own OS; applies on next ROM load)",
                       variable=self.accurate_var, bg=CATHLE_WIN_GRAY,
                       font=UI_FONT).pack(anchor="w", padx=13, pady=3)

        directories = tabs["Directories"]
        rom_box = tk.LabelFrame(directories, text=" Rom Directory ",
                                bg=CATHLE_WIN_GRAY, font=UI_FONT)
        rom_box.pack(fill=tk.X, padx=9, pady=9)
        directory_entry = tk.Entry(rom_box, textvariable=self.rom_directory_var,
                                   font=UI_FONT, relief=tk.SUNKEN)
        directory_entry.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=7, pady=9)
        tk.Button(rom_box, text="...", width=3, font=UI_FONT,
                  command=self.choose_rom_directory).pack(side=tk.LEFT, padx=(0, 7), pady=9)
        for label in ("N64 Auto saves:  In-memory (single-file mode)",
                      "Instant saves:  In-memory slots",
                      "Screenshots:  Ask when captured"):
            tk.Label(directories, text=label, bg=CATHLE_WIN_GRAY,
                     font=UI_FONT, anchor=tk.W).pack(fill=tk.X, padx=15, pady=5)

        plugins = tabs["Plugins"]
        plugin_values = (
            ("Graphics:", "HLE F3D/F3DEX/F3DEX2/S2DEX + software RDP"),
            ("Audio:", f"cathle audio engine ({CATHLE_AUDIO_ENGINE}) — live HLE ABI1 → pygame-ce"),
            ("Controller:", "Keyboard + pygame-ce gamepad (if installed)"),
            ("Reality Signal Processor:", "HLE known ucodes + LLE RSP fallback"),
        )
        for row, (label, value) in enumerate(plugin_values):
            box = tk.LabelFrame(plugins, text=f" {label} ", bg=CATHLE_WIN_GRAY, font=UI_FONT)
            box.pack(fill=tk.X, padx=9, pady=(7 if row == 0 else 2, 2))
            combo = ttk.Combobox(box, values=(value,), state="readonly")
            combo.set(value)
            combo.pack(fill=tk.X, padx=7, pady=5)

        # Input: click a button, then press the key to bind it to that N64 control.
        inp = tabs["Input"]
        key_vars: Dict[str, Any] = {}
        grid = tk.Frame(inp, bg=CATHLE_WIN_GRAY)
        grid.pack(fill=tk.BOTH, expand=True, padx=9, pady=6)
        def capture(name):
            key_vars[name].set("press a key…")
            def got(event, n=name):
                key_vars[n].set(event.keysym)
                dialog.unbind("<KeyPress>")
                return "break"
            dialog.bind("<KeyPress>", got)
            dialog.focus_set()
        for idx, name in enumerate(DEFAULT_KEYMAP):
            r, c = idx % 9, (idx // 9) * 3
            key_vars[name] = tk.StringVar(value=self.keymap.get(name, ""))
            tk.Label(grid, text=name.replace("_", " ").title() + ":", bg=CATHLE_WIN_GRAY, font=UI_FONT,
                     anchor=tk.W, width=11).grid(row=r, column=c, sticky="w", pady=1)
            tk.Button(grid, textvariable=key_vars[name], width=10, font=UI_FONT,
                      command=lambda n=name: capture(n)).grid(row=r, column=c + 1, padx=(0, 12), pady=1)
        tk.Button(inp, text="Defaults", font=UI_FONT,
                  command=lambda: [key_vars[k].set(v) for k, v in DEFAULT_KEYMAP.items()]).pack(anchor="e", padx=9, pady=3)

        buttons = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        buttons.pack(fill=tk.X, padx=7, pady=(0, 7))

        def apply_settings(close=False):
            for name, var in key_vars.items():
                val = var.get()
                if val and val != "press a key…":
                    self.keymap[name] = val
            save_keymap(self.keymap)
            self.limit_fps = bool(self.limit_fps_var.get())
            self.emu_speed = DEFAULT_EMU_SPEED
            self._persist_ui_prefs()
            new_dir = self.rom_directory_var.get().strip()
            if new_dir and os.path.isdir(new_dir) and new_dir != self.browser.directory:
                self.browser.scan_roms(new_dir)
            self._set_status("Settings applied")
            if close:
                dialog.destroy()

        tk.Button(buttons, text="OK", width=10, font=UI_FONT,
                  command=lambda: apply_settings(True)).pack(side=tk.RIGHT, padx=3)
        tk.Button(buttons, text="Cancel", width=10, font=UI_FONT,
                  command=dialog.destroy).pack(side=tk.RIGHT, padx=3)
        tk.Button(buttons, text="Apply", width=10, font=UI_FONT,
                  command=apply_settings).pack(side=tk.RIGHT, padx=3)

    def show_registers(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("R4300i Registers")
        dialog.geometry("460x520")
        tree = ttk.Treeview(dialog, columns=("register", "value"), show="headings")
        tree.heading("register", text="Register")
        tree.heading("value", text="Value")
        tree.column("register", width=170)
        tree.column("value", width=250)
        tree.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        def refresh():
            for item in tree.get_children():
                tree.delete(item)
            with self._core_lock:
                for index, value in enumerate(self.core.cpu.gpr):
                    tree.insert("", tk.END, values=(f"GPR r{index:02d}", f"0x{value:016X}"))
                tree.insert("", tk.END, values=("PC", f"0x{self.core.cpu.pc:08X}"))
                tree.insert("", tk.END, values=("HI", f"0x{self.core.cpu.hi:016X}"))
                tree.insert("", tk.END, values=("LO", f"0x{self.core.cpu.lo:016X}"))
                for index, value in enumerate(self.core.cpu.cp0):
                    name = R4300_CP0_REG_NAMES.get(index, f"CP0 {index}")
                    tree.insert("", tk.END, values=(name, f"0x{value:08X}"))
        refresh()
        tk.Button(dialog, text="Refresh", command=refresh, font=UI_FONT,
                  width=10).pack(side=tk.RIGHT, padx=6, pady=(0, 6))

    def show_memory(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("Memory")
        dialog.geometry("720x430")
        controls = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        controls.pack(fill=tk.X)
        tk.Label(controls, text="Address:", bg=CATHLE_WIN_GRAY,
                 font=UI_FONT).pack(side=tk.LEFT, padx=(6, 2), pady=6)
        address = tk.Entry(controls, font=UI_FONT_MONO, width=14)
        address.insert(0, "80000000")
        address.pack(side=tk.LEFT, pady=6)
        output = tk.Text(dialog, font=UI_FONT_MONO, bg="#ffffff", fg="#000000",
                         wrap=tk.NONE, relief=tk.SUNKEN)
        output.pack(fill=tk.BOTH, expand=True, padx=5, pady=(0, 5))

        def refresh():
            try:
                virtual = int(address.get().strip().replace("0x", ""), 16)
            except ValueError:
                return
            physical = self.core.bus.v_to_p(virtual)
            lines = []
            with self._core_lock:
                for row in range(16):
                    start = physical + row * 16
                    chunk = self.core.rdram[start:start + 16] if 0 <= start < RDRAM_SIZE else b""
                    hexes = " ".join(f"{value:02X}" for value in chunk).ljust(47)
                    ascii_text = "".join(chr(value) if 32 <= value < 127 else "." for value in chunk)
                    lines.append(f"{(virtual + row * 16) & MASK_32:08X}  {hexes}  {ascii_text}")
            output.delete("1.0", tk.END)
            output.insert("1.0", "\n".join(lines))
        tk.Button(controls, text="View", command=refresh, width=8,
                  font=UI_FONT).pack(side=tk.LEFT, padx=4, pady=6)
        refresh()

    def show_tlb(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("TLB")
        dialog.geometry("760x430")
        columns = ("index", "vpn2", "mask", "asid", "pfn0", "pfn1", "valid")
        tree = ttk.Treeview(dialog, columns=columns, show="headings")
        for key in columns:
            tree.heading(key, text=key.upper())
            tree.column(key, width=95, anchor=tk.CENTER)
        tree.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        with self._core_lock:
            for index, entry in enumerate(self.core.cpu.tlb):
                tree.insert("", tk.END, values=(
                    index, f"{entry.vpn2:05X}", f"{entry.mask:08X}", entry.asid,
                    f"{entry.pfn0:05X}", f"{entry.pfn1:05X}",
                    f"{int(entry.v0)}/{int(entry.v1)}"
                ))

    def set_breakpoint(self):
        value = simpledialog.askstring("Set Breakpoint", "Virtual address (hex):",
                                       parent=self.root)
        if value:
            try:
                address = int(value.replace("0x", ""), 16) & MASK_32
                self._set_status(f"Breakpoint display set at 0x{address:08X}")
            except ValueError:
                messagebox.showerror("Set Breakpoint", "Enter a hexadecimal address.")

    def show_cheats(self):
        if not self.core.rom:
            return
        dialog = tk.Toplevel(self.root)
        dialog.title("Cheats")
        dialog.geometry("500x340")
        frame = tk.Frame(dialog, bg=CATHLE_WIN_GRAY)
        frame.pack(fill=tk.BOTH, expand=True, padx=6, pady=6)
        listing = tk.Listbox(frame, font=UI_FONT, bg="#ffffff", selectbackground=CATHLE_LIST_SEL_BG,
                             selectforeground=CATHLE_LIST_SEL_FG)
        listing.pack(fill=tk.BOTH, expand=True)

        def refresh():
            listing.delete(0, tk.END)
            for cheat in self.core.cheat_engine.codes:
                listing.insert(tk.END, f"[{'x' if cheat.enabled else ' '}] {cheat.name}    {cheat.code}")

        def add():
            name = simpledialog.askstring("Add Cheat", "Name:", parent=dialog)
            if not name:
                return
            code = simpledialog.askstring("Add Cheat", "Code (AAAAAAAA VVVVVVVV):",
                                          parent=dialog)
            if code:
                self.core.cheat_engine.add(name, code)
                refresh()

        def toggle():
            selection = listing.curselection()
            if selection:
                self.core.cheat_engine.toggle(selection[0])
                refresh()

        def remove():
            selection = listing.curselection()
            if selection:
                del self.core.cheat_engine.codes[selection[0]]
                self.core.cheat_engine.active = [c for c in self.core.cheat_engine.codes if c.enabled]
                refresh()

        buttons = tk.Frame(frame, bg=CATHLE_WIN_GRAY)
        buttons.pack(fill=tk.X, pady=(5, 0))
        for text, command in (("Add New Cheat...", add), ("Enable/Disable", toggle),
                              ("Delete", remove), ("Close", dialog.destroy)):
            tk.Button(buttons, text=text, command=command, font=UI_FONT).pack(
                side=tk.LEFT, padx=(0, 4))
        refresh()

    def show_about(self):
        messagebox.showinfo(
            "About cathle",
            f"{APP_NAME}\n"
            f"N64 High Level Emulator\n"
            f"{COPYRIGHT_LINE}\n\n"
            "N64 R4300i emulator core\n"
            "cathle classic interface\n"
            "Single-file Python 3.14 build\n\n"
            "Core, tools, browser, and interface\n"
            "presented under the cathle name."
        )

    def _on_close(self):
        try:
            with self._core_lock:
                self.core.flush_saves()
        except Exception:
            pass
        self.running = False
        self.core.running = False
        self._worker_stop.set()
        self._worker_wake.set()
        if self.audio_out is not None:
            try:
                self.audio_out.close()
            except Exception:
                pass
            self.audio_out = None
        if self.root:
            root = self.root
            self.root = None
            root.destroy()

    def run(self):
        if self.root:
            self.root.mainloop()


def list_implemented_opcodes():
    """Return sorted names of every VR4300 opcode with a live dispatch handler."""
    names = []
    for op, (name, fmt) in PRIMARY_OPS.items():
        if fmt is None:
            continue
        if name == "SPECIAL":
            for f, (n, ff) in SPECIAL_OPS.items():
                if ff is not None and _DISPATCH[_ID_SPECIAL | f] is not None:
                    names.append(n)
        elif name == "REGIMM":
            for rt, (n, ff) in REGIMM_OPS.items():
                if ff is not None and _DISPATCH[_ID_REGIMM | rt] is not None:
                    names.append(n)
        elif name == "COP0":
            for rs, (n, ff) in COP0_RS.items():
                if n == "COP0_CO":
                    for cf, (cn, cff) in COP0_CO.items():
                        if cff is not None and _DISPATCH[_ID_COP0_CO | cf] is not None:
                            names.append(cn)
                elif ff is not None and _DISPATCH[_ID_COP0_RS | rs] is not None:
                    names.append(n)
        elif name == "COP1":
            for rs, (n, ff) in COP1_RS.items():
                if n in ("S", "D", "W", "L"):
                    for f, (fn, ffmt) in COP1_FUNCT.items():
                        if ffmt is not None:
                            names.append(f"{fn}.{n}")
                elif n == "BC1":
                    names.append("BC1")
                elif ff is not None and _DISPATCH[_ID_COP1_RS | rs] is not None:
                    names.append(n)
        else:
            if _DISPATCH[_ID_PRIMARY | op] is not None:
                names.append(name)
    # BC1 dispatch slots
    if any(_DISPATCH[_ID_COP1_BC | rt] is not None for rt in range(4)):
        if "BC1" not in names:
            names.append("BC1")
    return sorted(set(names))


def assert_opcode_table():
    """Every non-reserved primary/special/regimm/cop slot must have a handler."""
    missing = []
    for op, (name, fmt) in PRIMARY_OPS.items():
        if name in ("SPECIAL", "REGIMM", "COP0", "COP1"):
            continue
        if fmt is None:
            # reserved primary — must raise RI
            h = _DISPATCH[_ID_PRIMARY | op]
            if h is None:
                missing.append(f"PRIMARY.{name}")
            continue
        if name in ("COP2", "COP3"):
            if _DISPATCH[_ID_PRIMARY | op] is None:
                missing.append(name)
            continue
        if _DISPATCH[_ID_PRIMARY | op] is None:
            missing.append(name)
    for f, (name, fmt) in SPECIAL_OPS.items():
        if _DISPATCH[_ID_SPECIAL | f] is None:
            missing.append(f"SPECIAL.{name}")
    for rt, (name, fmt) in REGIMM_OPS.items():
        if fmt is None:
            if _DISPATCH[_ID_REGIMM | rt] is None:
                missing.append(f"REGIMM.{name}")
        elif _DISPATCH[_ID_REGIMM | rt] is None:
            missing.append(f"REGIMM.{name}")
    for rs, (name, fmt) in COP0_RS.items():
        if name == "COP0_CO":
            continue
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP0_RS | rs] is None:
            missing.append(f"COP0.{name}")
    for cf, (name, fmt) in COP0_CO.items():
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP0_CO | cf] is None:
            missing.append(f"COP0.{name}")
    for rs, (name, fmt) in COP1_RS.items():
        if name in ("S", "D", "W", "L", "BC1"):
            continue
        if fmt is None:
            continue
        if _DISPATCH[_ID_COP1_RS | rs] is None:
            missing.append(f"COP1.{name}")
    for rt in range(4):
        if _DISPATCH[_ID_COP1_BC | rt] is None:
            missing.append(f"BC1.rt{rt}")
    for fid in (_ID_FPU_S, _ID_FPU_D, _ID_FPU_W, _ID_FPU_L):
        for f in COP1_FUNCT:
            if _DISPATCH[_ID_FPU | (fid << 6) | f] is None:
                missing.append(f"FPU.{fid}.{f:02X}")
    if missing:
        raise AssertionError("Missing dispatch handlers: " + ", ".join(missing[:40]))


# ── Compatibility harness (--boot-test) ──
COMPAT_RATINGS = ("Fails", "Boots", "Title", "In-game", "Playable")
COMPAT_DEFAULT_FRAMES = 1800
COMPAT_DEFAULT_STEPS = INTERP_BOOT_STEPS
COMPAT_HANG_STEPS = 5_000_000
COMPAT_MIN_HASHES = 3
# Controller button bits as returned by Joybus cmd 0x01 (big-endian 16-bit).
PAD_BUTTONS = {
    "A": 0x8000, "B": 0x4000, "Z": 0x2000, "START": 0x1000,
    "DUP": 0x0800, "DDOWN": 0x0400, "DLEFT": 0x0200, "DRIGHT": 0x0100,
    "L": 0x0020, "R": 0x0010, "CUP": 0x0008, "CDOWN": 0x0004, "CLEFT": 0x0002, "CRIGHT": 0x0001,
}


def compat_rating_rank(rating: str) -> int:
    try:
        return COMPAT_RATINGS.index(rating)
    except ValueError:
        return 0


def compat_rom_key(rom: bytes) -> str:
    """CRC1-CRC2 from the (normalized) cartridge header."""
    return f"{be32(rom, 0x10):08X}-{be32(rom, 0x14):08X}"


def compat_classify(lit: bool, distinct_hashes: int, error: str = "", hang: str = "") -> str:
    if error or hang:
        return "Fails"
    if lit and distinct_hashes >= COMPAT_MIN_HASHES:
        return "Boots"
    return "Fails"


def compat_parse_script(text: str, with_stick: bool = False):
    """Input script lines: ``<frame> BTN[,BTN...]|- [hold] [stick_x] [stick_y]``; ``# key: value`` headers.

    Returns (frame -> pad bits, headers), or (frame -> (bits, x, y), headers) when ``with_stick``.
    A press is held for ``hold`` frames (default 5); ``-`` means no buttons (stick only).
    """
    pads: Dict[int, Any] = {}
    meta: Dict[str, str] = {}
    for raw in text.splitlines():
        line = raw.strip()
        if not line:
            continue
        if line.startswith("#"):
            if ":" in line:
                k, v = line[1:].split(":", 1)
                meta[k.strip().lower()] = v.strip()
            continue
        parts = line.split()
        frame = int(parts[0])
        bits = 0
        if len(parts) > 1 and parts[1] != "-":
            for name in parts[1].split(","):
                name = name.strip().upper()
                if name and name not in PAD_BUTTONS:
                    raise ValueError(f"unknown button {name!r} in input script")
                bits |= PAD_BUTTONS.get(name, 0)
        hold = int(parts[2]) if len(parts) > 2 else 5
        sx = int(parts[3]) if len(parts) > 3 else 0
        sy = int(parts[4]) if len(parts) > 4 else 0
        for f in range(frame, frame + max(1, hold)):
            ob, ox, oy = pads.get(f, (0, 0, 0))
            pads[f] = (ob | bits, sx or ox, sy or oy)
    if with_stick:
        return pads, meta
    return {f: v[0] for f, v in pads.items()}, meta


def _compat_interrupts_masked(cpu) -> bool:
    st = cpu.cp0[CP0_STATUS]
    return not (st & STATUS_IE) or bool(st & (STATUS_EXL | STATUS_ERL)) or not (st & 0xFF00)


def compat_run_rom(path: str, frames: int = COMPAT_DEFAULT_FRAMES, steps: int = COMPAT_DEFAULT_STEPS,
                   dump_frames: Tuple[int, ...] = (), compat_dir: str = "compat", os_mode: str = "lle",
                   ram_mb: int = 8, verify_audio: int = 0, verify_gfx: int = 0) -> Dict[str, Any]:
    """Boot one ROM headlessly for ``frames`` VI frames; return a report row."""
    import hashlib, traceback
    random.seed(0)
    t0 = time.perf_counter()
    row: Dict[str, Any] = {"path": path, "file": os.path.basename(path), "frames_run": 0,
                           "first_lit_frame": None, "distinct_hashes": 0, "final_pc": None,
                           "error": "", "hang": "", "unimplemented": {}, "os_mode": os_mode}
    core = ACsN64Core()
    core.save_dir = None  # harness runs must not read or write battery saves
    core.ram_mb = ram_mb
    core.use_jit = not os.environ.get("CATHLE_NO_JIT")
    core.audio_verify = verify_audio
    core.gfx_verify = verify_gfx
    # HLE-OS frames are a fixed instruction budget; accurate-mode frames end at the VI interrupt.
    core.fixed_steps = steps if os_mode == "hle" else None
    err = core.load_rom(path, lle=(os_mode == "lle"))
    if err:
        row.update(error=f"load: {err}", rating="Fails", key="", wall_s=round(time.perf_counter() - t0, 2))
        return row
    rom = core.rom
    hdr = core.rom_header
    key = compat_rom_key(rom)
    row.update(key=key, name=(getattr(hdr, "title", "") or "").strip(),
               game_code=bytes(rom[0x3B:0x3F]).decode("ascii", "replace"),
               region=_COUNTRY_NAMES.get(rom[0x3E], f"0x{rom[0x3E]:02X}"),
               cic=_CIC_NAMES.get(core.cic, str(core.cic)),
               save_type={SAVE_AUTO: "none", SAVE_EEPROM_4K: "EEPROM 4K", SAVE_EEPROM_16K: "EEPROM 16K",
                          SAVE_SRAM: "SRAM", SAVE_FLASHRAM: "FlashRAM"}.get(core.save_mgr.save_type, "?"))
    pads: Dict[int, int] = {}
    meta: Dict[str, str] = {}
    spath = os.path.join(compat_dir, "scripts", f"{key}.txt")
    if os.path.isfile(spath):
        with open(spath) as f:
            pads, meta = compat_parse_script(f.read(), with_stick=True)
    goldens: Dict[int, str] = {}
    gdir = os.path.join(compat_dir, "golden")
    if os.path.isdir(gdir):
        for name in os.listdir(gdir):
            if name.startswith(key + "_") and name.endswith(".sha1"):
                n = int(name[len(key) + 1:-5])
                with open(os.path.join(gdir, name)) as f:
                    goldens[n] = f.read().split()[0].strip().lower()
    # A script may need more frames than the sweep default (e.g. to reach gameplay).
    if meta.get("frames", "").isdigit():
        frames = max(frames, int(meta["frames"]))
    want_frames = set(dump_frames) | set(goldens)
    hashes = set()
    golden_ok: List[int] = []
    hang_win = -1
    hang_steps = 0
    hang_mem = b""
    core.running = True
    try:
        for f in range(frames):
            core.set_pad(0, *pads.get(f, (0, 0, 0)))
            core.step_frame()
            row["frames_run"] = f + 1
            ppm = core.fb_ppm
            if ppm:
                hashes.add(hashlib.sha1(ppm).hexdigest())
                if core.fb_lit and row["first_lit_frame"] is None:
                    row["first_lit_frame"] = f
            if f in want_frames and ppm:
                digest = hashlib.sha1(ppm).hexdigest()
                if f in dump_frames:
                    fdir = os.path.join(compat_dir, "frames")
                    os.makedirs(fdir, exist_ok=True)
                    with open(os.path.join(fdir, f"{key}_{f}.ppm"), "wb") as out:
                        out.write(ppm)
                if goldens.get(f) == digest:
                    golden_ok.append(f)
            # Hang = same 64-byte PC window, interrupts masked, and RDRAM frozen.
            # (UltraHLE's idle thread spins masked while OS HLE still moves memory.)
            win = core.cpu.pc & ~0x3F
            if win == hang_win and _compat_interrupts_masked(core.cpu):
                steps_this = steps if core.fixed_steps else core.vi_frame_len()
                mem = hashlib.sha1(core.rdram).digest()
                if mem == hang_mem:
                    hang_steps += steps_this
                    if hang_steps > COMPAT_HANG_STEPS:
                        pc = core.cpu.pc & MASK_32
                        # `b .` / `j .` with interrupts off after drawing = deliberate halt (test ROMs).
                        # The PC may be on the branch or its delay slot.
                        def _self_branch(at):
                            w = core.bus.read_u32(at)
                            return w == 0x1000FFFF or (w >> 26 == 2 and ((w & 0x3FFFFFF) << 2) == (at & 0x0FFFFFFF))
                        halt = _self_branch(pc) or _self_branch(u32(pc - 4))
                        if halt and row["first_lit_frame"] is not None:
                            row["halt"] = f"halt@{pc:08X}"
                        else:
                            row["hang"] = f"hang@{pc:08X}"
                        break
                else:
                    hang_mem, hang_steps = mem, 0
            else:
                hang_win, hang_steps, hang_mem = win, 0, b""
    except Exception as e:  # one bad ROM must never stop a sweep
        tb = traceback.extract_tb(e.__traceback__)
        where = f"{tb[-1].name}:{tb[-1].lineno}" if tb else "?"
        row["error"] = f"{type(e).__name__}: {e} @ {where}"
    row["final_pc"] = f"{core.cpu.pc & MASK_32:08X}"
    row["distinct_hashes"] = len(hashes)
    row["unimplemented"] = dict(sorted(core.unimpl.items(), key=lambda kv: -kv[1]))
    if core.gfx_verify_log:
        log = core.gfx_verify_log
        row["gfx_verify"] = {"ucode": log[0]["ucode"], "tasks": len(log),
                             "max_diff_pct": max(e["diff_pct"] for e in log),
                             "max_mean_err": max(e["mean_err"] for e in log),
                             "errors": sorted({e["error"] for e in log if e["error"]})}
    if core.audio_verify_log:
        log = core.audio_verify_log
        row["audio_verify"] = {"ucode": log[0]["ucode"], "tasks": len(log),
                               "max_diff": max(e["max_diff"] for e in log),
                               "errors": sorted({e["error"] for e in log if e["error"]})}
    rating = compat_classify(row["first_lit_frame"] is not None, len(hashes), row["error"], row["hang"])
    if row.get("halt") and not row["error"]:
        rating = "Boots"  # drew a lit frame, then parked the CPU on purpose
    if rating != "Fails" and goldens and len(golden_ok) == len(goldens):
        target = meta.get("rating", "Title")
        if compat_rating_rank(target) > compat_rating_rank(rating) and target != "Playable":
            rating = target
    row["golden_matched"] = sorted(golden_ok)
    row["rating"] = rating
    row["wall_s"] = round(time.perf_counter() - t0, 2)
    return row


def compat_find_roms(target: str) -> List[str]:
    if os.path.isfile(target):
        return [target]
    out = []
    for root, _dirs, files in os.walk(target):
        for name in sorted(files):
            if name.lower().endswith(ROM_EXTENSIONS + (".zip",)):
                out.append(os.path.join(root, name))
    return sorted(out)


def _compat_worker(args, q):
    path, frames, steps, dumps, cdir, os_mode, ram_mb, verify_audio, verify_gfx = args
    if os.environ.get("CATHLE_NO_ACCEL"):
        globals()["USE_NUMPY"] = False
    try:
        q.put(compat_run_rom(path, frames, steps, dumps, cdir, os_mode, ram_mb, verify_audio, verify_gfx))
    except BaseException as e:
        q.put({"path": path, "file": os.path.basename(path), "key": "", "rating": "Fails",
               "error": f"worker: {type(e).__name__}: {e}"})


def compat_run_many(paths: List[str], frames: int, steps: int, dumps: Tuple[int, ...] = (),
                    jobs: int = 1, timeout_s: float = 600.0, compat_dir: str = "compat",
                    progress: Optional[Callable[[Dict[str, Any]], None]] = None,
                    os_mode: str = "lle", ram_mb: int = 8, verify_audio: int = 0,
                    verify_gfx: int = 0) -> List[Dict[str, Any]]:
    """Run ROMs in up to ``jobs`` processes; a ROM over ``timeout_s`` is killed and rated Fails."""
    if jobs <= 1:
        rows = []
        for p in paths:
            r = compat_run_rom(p, frames, steps, dumps, compat_dir, os_mode, ram_mb, verify_audio, verify_gfx)
            rows.append(r)
            if progress:
                progress(r)
        return rows
    import multiprocessing as mp
    ctx = mp.get_context("spawn")
    pending = list(paths)
    running: Dict[str, Tuple[Any, Any, float]] = {}
    rows_by_path: Dict[str, Dict[str, Any]] = {}
    while pending or running:
        while pending and len(running) < jobs:
            p = pending.pop(0)
            q = ctx.Queue()
            proc = ctx.Process(target=_compat_worker, args=((p, frames, steps, dumps, compat_dir, os_mode, ram_mb, verify_audio, verify_gfx), q), daemon=True)
            proc.start()
            running[p] = (proc, q, time.perf_counter())
        for p, (proc, q, started) in list(running.items()):
            row = None
            try:
                row = q.get(timeout=0.05)
            except Exception:
                if time.perf_counter() - started > timeout_s:
                    proc.kill()
                    row = {"path": p, "file": os.path.basename(p), "key": "", "rating": "Fails",
                           "error": "", "hang": "timeout", "wall_s": round(timeout_s, 2)}
                elif not proc.is_alive() and q.empty():
                    row = {"path": p, "file": os.path.basename(p), "key": "", "rating": "Fails",
                           "error": f"worker exited {proc.exitcode}"}
            if row is not None:
                proc.join(1)
                del running[p]
                rows_by_path[p] = row
                if progress:
                    progress(row)
    return [rows_by_path[p] for p in paths]


def compat_merge_manual(report: Dict[str, Dict[str, Any]], manual: Dict[str, Dict[str, Any]]):
    """Manual ratings (compat/manual.json) win when higher; the harness never overwrites them."""
    for key, m in manual.items():
        row = report.get(key)
        if row is None:
            continue
        row["manual"] = m
        mr = m.get("rating", "")
        if mr and compat_rating_rank(mr) > compat_rating_rank(row.get("rating", "Fails")):
            row["rating"] = mr


def compat_regressions(old: Dict[str, Dict[str, Any]], new: Dict[str, Dict[str, Any]]) -> List[str]:
    out = []
    for key, row in new.items():
        prev = old.get(key)
        if prev and compat_rating_rank(row.get("rating", "Fails")) < compat_rating_rank(prev.get("rating", "Fails")):
            out.append(f"{row.get('name') or row.get('file')} [{key}]: {prev.get('rating')} -> {row.get('rating')}")
    return out


def compat_report_md(report: Dict[str, Dict[str, Any]]) -> str:
    rows = sorted(report.values(), key=lambda r: (-compat_rating_rank(r.get("rating", "Fails")), r.get("name") or r.get("file", "")))
    counts = {k: 0 for k in COMPAT_RATINGS}
    for r in rows:
        counts[r.get("rating", "Fails")] = counts.get(r.get("rating", "Fails"), 0) + 1
    lines = [f"# {APP_NAME} compatibility report", "",
             " · ".join(f"{k}: {counts[k]}" for k in reversed(COMPAT_RATINGS)) + f" · total: {len(rows)}", "",
             "| Name | Region | CIC | Rating | First lit | Frames | Problem | Top unimplemented |",
             "|---|---|---|---|---|---|---|---|"]
    for r in rows:
        top = ", ".join(f"{k}×{v}" for k, v in list(r.get("unimplemented", {}).items())[:3])
        problem = r.get("error") or r.get("hang") or r.get("halt") or ""
        lit = r.get("first_lit_frame")
        lines.append(f"| {r.get('name') or r.get('file')} | {r.get('region', '')} | {r.get('cic', '')} | "
                     f"{r.get('rating')} | {'' if lit is None else lit} | {r.get('frames_run', '')} | "
                     f"{problem.replace('|', '/')} | {top.replace('|', '/')} |")
    return "\n".join(lines) + "\n"


def compat_tier_coverage(report: Dict[str, Dict[str, Any]], tiers: Dict[str, Any]) -> List[str]:
    """Lines summarising, per tier, which listed games were tested and how they rated."""
    def norm(t):
        return "".join(ch for ch in t.casefold() if ch.isalnum())
    lines = []
    for tier in ("tier1", "tier2", "tier3"):
        games = tiers.get(tier) or []
        if not games:
            continue
        counts = {k: 0 for k in COMPAT_RATINGS}; missing = []
        for g in games:
            match = None
            for r in report.values():
                if g.get("code") and r.get("game_code") == g["code"]:
                    match = r; break
                if not g.get("code") and r.get("name") and norm(r["name"])[:10] in norm(g["name"]):
                    match = r; break
            if match is None:
                missing.append(g["name"])
            else:
                counts[match.get("rating", "Fails")] += 1
        tested = len(games) - len(missing)
        rated = ", ".join(f"{k} {counts[k]}" for k in reversed(COMPAT_RATINGS) if counts[k])
        lines.append(f"{tier}: {tested}/{len(games)} have a local ROM" + (f" — {rated}" if rated else "") +
                     (f"; missing: {len(missing)}" if missing else ""))
    return lines


def _compat_load_json(path: str) -> Dict[str, Any]:
    import json
    if not path or not os.path.isfile(path):
        return {}
    with open(path) as f:
        return json.load(f)


def compat_main(argv: List[str]) -> int:
    import argparse, json
    ap = argparse.ArgumentParser(prog="cathle --boot-test", description="Headless boot/compat sweep")
    ap.add_argument("--boot-test", dest="target", required=True, help="ROM file or directory")
    ap.add_argument("--frames", type=int, default=COMPAT_DEFAULT_FRAMES)
    ap.add_argument("--steps-per-frame", type=int, default=COMPAT_DEFAULT_STEPS)
    ap.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--timeout", type=float, default=600.0)
    ap.add_argument("--dump-frame", type=int, action="append", default=[])
    ap.add_argument("--compare", default="", help="previous report.json; exit 1 on any rating drop")
    ap.add_argument("--compat-dir", default="compat")
    ap.add_argument("--no-write", action="store_true", help="do not write report files")
    ap.add_argument("--no-accel", action="store_true", help="disable numpy acceleration (pure Python)")
    ap.add_argument("--no-jit", action="store_true", help="interpret the CPU instead of the block JIT")
    ap.add_argument("--ram", type=int, choices=(4, 8), default=8, help="RDRAM MB (8 = Expansion Pak)")
    ap.add_argument("--verify-audio", type=int, default=0, metavar="N",
                    help="cross-check the first N audio tasks: HLE ABI1 vs the real ucode on the LLE RSP")
    ap.add_argument("--verify-gfx", type=int, default=0, metavar="N",
                    help="cross-check the first N graphics tasks: HLE vs the real ucode on the LLE RSP")
    ap.add_argument("--os", dest="os_mode", choices=("hle", "lle"), default="lle",
                    help="hle = cathle HLE OS patches; lle = run the game's own libultra (accurate)")
    a = ap.parse_args(argv)
    if a.no_accel:
        globals()["USE_NUMPY"] = False
        os.environ["CATHLE_NO_ACCEL"] = "1"
    if a.no_jit:
        os.environ["CATHLE_NO_JIT"] = "1"
    paths = compat_find_roms(a.target)
    if not paths:
        print(f"no ROMs found under {a.target}")
        return 1
    print(f"{APP_NAME}: boot-testing {len(paths)} ROM(s), {a.frames} frames × {a.steps_per_frame} steps, jobs={a.jobs}")
    def progress(r):
        av = r.get("audio_verify")
        avs = f" audio-verify ucode={av['ucode']} tasks={av['tasks']} max|diff|={av['max_diff']}" if av else ""
        gv = r.get("gfx_verify")
        if gv:
            avs += (f" gfx-verify ucode={gv['ucode']} tasks={gv['tasks']} visibly-different={gv['max_diff_pct']}%"
                    f" mean-err={gv['max_mean_err']} (5-bit steps)")
        print(f"  {r.get('rating', 'Fails'):8s} {r.get('name') or r.get('file')}  "
              f"lit={r.get('first_lit_frame')} pc={r.get('final_pc')} {r.get('error') or r.get('hang') or ''} "
              f"({r.get('wall_s', '?')}s){avs}", flush=True)
    rows = compat_run_many(paths, a.frames, a.steps_per_frame, tuple(a.dump_frame), a.jobs, a.timeout,
                           a.compat_dir, progress, a.os_mode, a.ram, a.verify_audio, a.verify_gfx)
    report = {(r.get("key") or r.get("file")): r for r in rows}
    compat_merge_manual(report, _compat_load_json(os.path.join(a.compat_dir, "manual.json")))
    old = _compat_load_json(a.compare)
    if not a.no_write:
        os.makedirs(a.compat_dir, exist_ok=True)
        # Keep rows for ROMs not in this run so partial runs don't erase history.
        merged = dict(_compat_load_json(os.path.join(a.compat_dir, "report.json")))
        merged.update(report)
        with open(os.path.join(a.compat_dir, "report.json"), "w") as f:
            json.dump(merged, f, indent=1, sort_keys=True)
        with open(os.path.join(a.compat_dir, "report.md"), "w") as f:
            f.write(compat_report_md(merged))
    tiers = _compat_load_json(os.path.join(a.compat_dir, "tiers.json"))
    if tiers:
        for line in compat_tier_coverage(report, tiers):
            print("  " + line)
    regress = compat_regressions(old, report) if old else []
    for line in regress:
        print(f"REGRESSION: {line}")
    if regress:
        return 1
    return 0 if all(compat_rating_rank(r.get("rating", "Fails")) >= 1 for r in rows) else 1


def _selftest_jit_fpu() -> None:
    """Block JIT ≡ interpreter for inlined COP1 (S/D/W, both Status.FR modes) and 64-bit loads/stores."""
    def i_(op, rs, rt, imm): return (op << 26) | (rs << 21) | (rt << 16) | (imm & 0xFFFF)
    def c1(fmt, ft, fs, fd, funct): return (0x11 << 26) | (fmt << 21) | (ft << 16) | (fs << 11) | (fd << 6) | funct
    S, D, W = 0x10, 0x11, 0x14
    prog = [
        i_(0x0F, 0, 8, 0x8000), i_(0x0D, 8, 8, 0x2000), i_(0x09, 0, 9, -7),
        i_(0x31, 8, 0, 0), i_(0x31, 8, 1, 4), i_(0x31, 8, 2, 8),
        c1(S, 1, 0, 4, 0x00), c1(S, 2, 1, 5, 0x01), c1(S, 2, 0, 6, 0x02), c1(S, 1, 0, 7, 0x03),
        c1(S, 0, 0, 8, 0x04), c1(S, 0, 1, 9, 0x05), c1(S, 0, 0, 10, 0x07), c1(S, 0, 4, 11, 0x06),
        c1(S, 1, 0, 0, 0x3C), c1(S, 0, 0, 12, 0x21), i_(0x35, 8, 14, 16),
        c1(D, 14, 12, 16, 0x00), c1(D, 14, 16, 18, 0x02), c1(D, 14, 18, 20, 0x03), c1(D, 12, 20, 22, 0x01),
        c1(D, 0, 22, 24, 0x20), c1(D, 0, 18, 25, 0x0D), c1(D, 14, 16, 0, 0x3E), c1(D, 0, 16, 30, 0x06),
        c1(S, 3, 0, 13, 0x03),   # x / 0.0: the handler sets FCR31 cause; the next COP1 op must clear it
        (0x11 << 26) | (0x04 << 21) | (9 << 16) | (26 << 11), c1(W, 0, 26, 27, 0x20), c1(W, 0, 26, 28, 0x21),
        (0x11 << 26) | (10 << 16) | (27 << 11), (0x11 << 26) | (11 << 16) | (1 << 11),
        i_(0x3D, 8, 18, 24), i_(0x39, 8, 5, 32), i_(0x37, 8, 12, 16), i_(0x3F, 8, 12, 40),
    ]
    base = 0x1000
    loop = 0x80000000 | (base + 4 * len(prog))
    prog += [(0x02 << 26) | ((loop >> 2) & 0x3FFFFFF), 0]
    data = struct.pack(">fff", 1.5, -2.25, 4.0) + bytes(4) + struct.pack(">d", 3.125)
    def machine(fr):
        c = ACsN64Core()
        for k, w in enumerate(prog):
            put_be32(c.rdram, base + 4 * k, w)
        c.rdram[0x2000:0x2000 + len(data)] = data
        c.cpu.cp0[CP0_STATUS] = STATUS_CU1 | (STATUS_FR if fr else 0)
        c.cpu.pc = 0x80000000 | base; c.cpu.next_pc = c.cpu.pc + 4
        return c
    def state(c):
        cpu = c.cpu
        return (list(cpu.gpr), list(cpu.fpr), cpu.fcr31, cpu.cp0[CP0_COUNT], cpu.pc, bytes(c.rdram[0x2000:0x2040]))
    for fr in (False, True):
        ref = machine(fr)
        for _ in range(len(prog)):
            ref.cpu.step()
        for compile_fr in (False, True):   # also runs the lazily built other-FR variant
            j = machine(compile_fr)
            assert j.jit.compile(j.cpu.pc) is not None
            j.cpu.cp0[CP0_STATUS] = STATUS_CU1 | (STATUS_FR if fr else 0)
            assert j._run_blocks(1) == len(prog)
            assert state(j) == state(ref), f"JIT/interpreter mismatch (FR={fr}, compiled FR={compile_fr})"


def _selftest_frameskip() -> None:
    """Frame-skip policy: only displayed colour images count as frames; never skips render targets."""
    c = ACsN64Core()
    assert c.frameskip == normalize_frameskip(os.environ.get("CATHLE_FRAMESKIP", "off"))
    c.frameskip = "1"; c._fs_reset()
    A, B, Z, RT = 0x100000, 0x125800, 0x400, 0x200000
    for a in (A, B, Z, RT):
        c._fs_on_cimg(a, 640)
    assert not c.rdp.fs_skip and c.frames_skipped == 0        # nothing displayed yet → draw everything
    assert c._fs_origin_stale(A + 0x280) is False and c._fs_origin_stale(B + 0x280) is False
    assert c._fs_display == {A, B}                            # nearest buffer, not the overlapping one
    seq = []
    for a in (Z, A, Z, B, RT, B, Z, A, Z, B):
        c._fs_on_cimg(a, 640)
        seq.append(c.rdp.fs_skip)
    # "Skip 1" alternates: A skipped, B drawn (render targets/depth clears always drawn), A skipped, B drawn.
    assert seq == [False, True, False, False, False, False, False, True, False, False], seq
    assert c._fs_origin_stale(A + 0x280) and not c._fs_origin_stale(B + 0x280)
    c.frameskip = "off"; c._fs_reset(); c._fs_on_cimg(A, 640); assert not c.rdp.fs_skip


def self_test() -> int:
    assert_opcode_table()
    names = list_implemented_opcodes()
    # Smoke-test a handful of handlers through the CPU.
    core = ACsN64Core()
    cpu = core.cpu
    g = cpu.gpr
    # LUI + ORI
    cpu.execute(N64Opcode(0x3C010123)); assert (g[1] & MASK_32) == 0x01230000
    cpu.execute(N64Opcode(0x34215678)); assert (g[1] & MASK_32) == 0x01235678
    # ADDU
    g[2] = 5; g[3] = 7
    cpu.execute(N64Opcode(0x00431021)); assert sign32(g[2]) == 12
    # FPU CVT.S.W + ADD.S
    cpu.cp0[CP0_STATUS] |= STATUS_CU1
    cpu.fpr[0] = u64(4)  # word 4
    cpu.execute(N64Opcode(0x46800020))  # CVT.S.W f0, f0  (fmt=W=20? rs=0x14 -> W, funct=0x20)
    # BC1 dispatch must not RI
    cpu.fcr31 |= (1 << FCR31_COND_BIT)
    old_pc = cpu.pc
    cpu.next_pc = u32(old_pc + 4)
    cpu.execute(N64Opcode(0x45010004))  # BC1T +4
    # RECIP.S present in table
    assert any(n.startswith("RECIP") for n in names)
    assert any(n.startswith("RSQRT") for n in names)
    assert "ERET" in names and "CACHE" in names and "SYNC" in names and "WAIT" in names
    # UltraHLE OP_PATCH / OP_GROUP surface
    assert "PATCH" in names and "GROUP" in names
    assert len(ULTRAHLE_PATCH_TABLE) >= 61
    assert set(ULTRAHLE_PATCH_TABLE) == set(ULTRAHLE_PATCH_NAMES)
    # PATCH(4)=__ll_mul / dmultu: A0:A1 * A2:A3 -> V0:V1
    g[_UH_A0], g[_UH_A1] = 0, 6
    g[_UH_A2], g[_UH_A3] = 0, 7
    g[_UH_RA] = 0x80001000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(4)))
    assert g[_UH_V0] == 0 and g[_UH_V1] == 42
    assert cpu.pc == 0x80001000 and cpu.next_pc == 0x80001004
    # PATCH(56)=memcpy
    core.rdram[0:8] = b"\x11\x22\x33\x44\x55\x66\x77\x88"
    g[_UH_A0], g[_UH_A1], g[_UH_A2] = 0x80000010, 0x80000000, 8
    g[_UH_RA] = 0x80002000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(56)))
    assert bytes(core.rdram[0x10:0x18]) == b"\x11\x22\x33\x44\x55\x66\x77\x88"
    # PATCH(57)=osEepromProbe + PATCH(59/58) write/read round-trip
    core.save_mgr.save_type = SAVE_EEPROM_4K
    core.save_mgr.eeprom[:] = bytearray(EEPROM_16K_SIZE)
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(57)))
    assert g[_UH_V0] == EEPROM_TYPE_4K
    core.rdram[0x40:0x48] = b"\xDE\xAD\xBE\xEF\xCA\xFE\xF0\x0D"
    g[_UH_A1], g[_UH_A2] = 3, 0x80000040
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(59)))
    assert g[_UH_V0] == 0
    core.rdram[0x50:0x58] = b"\x00" * 8
    g[_UH_A1], g[_UH_A2] = 3, 0x80000050
    g[_UH_RA] = 0x80003000
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(make_ultrahle_patch(58)))
    assert g[_UH_V0] == 0
    assert bytes(core.rdram[0x50:0x58]) == b"\xDE\xAD\xBE\xEF\xCA\xFE\xF0\x0D"
    # GROUP is a no-op
    cpu.pc = 0x80000000; cpu.next_pc = 0x80000004
    cpu.execute(N64Opcode(u32((ULTRAHLE_OP_GROUP << 26) | 1)))
    assert cpu.pc == 0x80000004
    # install_patch helper writes the UltraHLE encoding
    core.ultrahle.install_patch(0x80000100, 23)
    assert core.bus.read_u32(0x80000100) == make_ultrahle_patch(23)
    # UltraHLE SYM / OSCALL database present
    assert len(ULTRAHLE_OSCALL) >= 200
    assert len(ULTRAHLE_OSPATCH) >= 50
    assert "osPiStartDma" not in ULTRAHLE_DISABLE_PATCHES
    assert ultrahle_match_ini("SUPER MARIO 64")["ismario"] == 1
    assert ultrahle_match_ini("Banjo-Kazooie")["bootloader"] == 1
    assert any(e[3] == 57 for e in ULTRAHLE_OSCALL if "osEepromProbe" in e[4])
    # IPL3 HLE must DMA cart[0x1000..] → RDRAM[entry], not a 1:1 rom copy.
    boot_rom = bytearray(0x2000)
    boot_rom[0:4] = Z64_MAGIC
    put_be32(boot_rom, 0x08, 0x80000400)
    boot_rom[0x20:0x34] = b"BOOTTEST\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00"
    put_be32(boot_rom, 0x1000, 0x3C1D8040)  # lui sp, 0x8040
    put_be32(boot_rom, 0x1004, 0x27BDFFF0)  # addiu sp, sp, -16
    core.rom = boot_rom
    core.rom_header = N64Header(boot_rom)
    core.cic = CIC_NUS_6102
    core._hle_ipl3_boot()
    assert be32(core.rdram, 0x400) == 0x3C1D8040
    assert be32(core.rdram, 0x404) == 0x27BDFFF0
    assert core.cpu.pc == 0x80000400
    assert core.bus.read_u32(0x80000400) == 0x3C1D8040
    # IPL3 copies exactly 1 MB: data past cart 0x101000 must not appear in RDRAM.
    big = bytearray(0x200000); big[:0x2000] = boot_rom; big[0x101000:0x101004] = b"\xAB\xCD\xEF\x01"
    core.rom = big; core._hle_ipl3_boot()
    assert be32(core.rdram, 0x400 + 0x100000) == 0
    core.rom = boot_rom; core._hle_ipl3_boot()
    core.cpu.execute(N64Opcode(core.bus.read_u32(core.cpu.pc)))
    assert (core.cpu.gpr[29] & MASK_32) == 0x80400000
    # 60 Hz frame pacing: one step_frame must raise VI and finish under ~2 frame periods.
    core.running = True
    t0 = time.perf_counter()
    steps = core.step_frame(budget_s=0.01)
    dt = time.perf_counter() - t0
    assert steps >= INTERP_MIN_STEPS
    assert core.frame_count >= 1
    assert core.bus.hw_interrupts & MI_INTR_VI
    assert dt < FRAME_PERIOD_NTSC * 3
    assert abs(core.frame_period - FRAME_PERIOD_NTSC) < 1e-6
    # COMPARE must arm IP7 only (never a fake SP interrupt).
    core.cpu.cp0[CP0_COMPARE] = u32(core.cpu.cp0[CP0_COUNT] + 1)
    core.cpu.cp0[CP0_CAUSE] &= ~CAUSE_IP7
    core.bus.hw_interrupts &= ~MI_INTR_SP
    core.cpu.step()
    assert core.cpu.cp0[CP0_CAUSE] & CAUSE_IP7
    assert not (core.bus.hw_interrupts & MI_INTR_SP)
    # CIC: IPL3 CRC32 identification, seeds, OS globals, 6105 challenge/response.
    import zlib
    blank = bytearray(0x2000)
    assert identify_cic(blank) == (CIC_NUS_6102, False)
    ipl = bytearray(0x2000); ipl[0x40:0x1000] = bytes(range(256)) * 15 + bytes(range(0xC0))
    CIC_IPL3_CRC32[zlib.crc32(bytes(ipl[0x40:0x1000]))] = CIC_NUS_6105
    try:
        assert identify_cic(ipl) == (CIC_NUS_6105, True)
    finally:
        del CIC_IPL3_CRC32[zlib.crc32(bytes(ipl[0x40:0x1000]))]
    for cic, seed in ((CIC_NUS_6101, 0x3F), (CIC_NUS_6102, 0x3F), (CIC_NUS_6103, 0x78),
                      (CIC_NUS_6105, 0x91), (CIC_NUS_6106, 0x85), (CIC_NUS_7102, 0x3F)):
        for country, tv in ((0x45, 1), (0x50, 0), (0x42, 2)):
            boot_rom[0x3E] = country
            core.rom = boot_rom; core.rom_header = N64Header(boot_rom); core.cic = cic
            core._hle_ipl3_boot()
            assert core.cpu.gpr[22] == seed, (cic, core.cpu.gpr[22])
            assert core.cpu.gpr[20] == tv and be32(core.rdram, 0x300) == tv
            assert be32(core.rdram, 0x318) == len(core.rdram) and be32(core.rdram, 0x308) == 0xB0000000
            assert (be32(core.rdram, 0x3F0) == len(core.rdram)) == (cic == CIC_NUS_6105)
            delta = {CIC_NUS_6103: 0x100000, CIC_NUS_6106: 0x200000}.get(cic, 0)
            assert core.cpu.pc == u32(0x80000400 - delta)
    boot_rom[0x3E] = 0x45
    # 6105 response is deterministic and stays within nibbles; PIF clears the control byte.
    rsp = cic_6105_response([i & 0xF for i in range(30)])
    assert len(rsp) == 30 and all(0 <= n <= 0xF for n in rsp)
    core.pif_ram[0x30:0x3F] = bytes(range(0x10, 0x1F)); core.pif_ram[0x3F] = 0x02
    core._pif_process_commands()
    assert core.pif_ram[0x3F] == 0 and core.pif_ram[0x2E] == 0
    # ── Accurate mode: precise exceptions, TLB, scheduler (US-007/US-008) ──
    def fresh():
        t = ACsN64Core(); t.lle = True; t.boot_lle(); t.running = True
        t.cpu.cp0[CP0_STATUS] = 0x34000000 | STATUS_CU1
        return t
    # Synchronous exception in a branch delay slot: EPC = branch, Cause.BD set.
    t = fresh(); c = t.cpu
    put_be32(t.rdram, 0x1000, 0x10000002)   # beq zero,zero,+2
    put_be32(t.rdram, 0x1004, 0x0000000C)   # syscall (delay slot)
    c.pc, c.next_pc = 0x80001000, 0x80001004
    c.step(); c.step()
    assert c.pc == 0x80000180 and c.cp0[CP0_EPC] == 0x80001000
    assert c.cp0[CP0_CAUSE] & CAUSE_BD and ((c.cp0[CP0_CAUSE] >> 2) & 0x1F) == 8
    # Same instruction outside a delay slot: EPC = itself, BD clear.
    t = fresh(); c = t.cpu
    put_be32(t.rdram, 0x1000, 0x0000000C)
    c.pc, c.next_pc = 0x80001000, 0x80001004
    c.step()
    assert c.cp0[CP0_EPC] == 0x80001000 and not (c.cp0[CP0_CAUSE] & CAUSE_BD)
    # Interrupt taken while the next instruction is a delay slot → EPC = branch, ExcCode 0.
    t = fresh(); c = t.cpu
    put_be32(t.rdram, 0x1000, 0x10000002); put_be32(t.rdram, 0x1004, 0)
    c.pc, c.next_pc = 0x80001000, 0x80001004
    c.cp0[CP0_CAUSE] = 0x7C  # stale ExcCode must be cleared
    c.step()
    c.cp0[CP0_STATUS] |= STATUS_IE | 0x0400
    t.bus.mi_intr_mask = MI_INTR_VI; t.bus.hw_interrupts = MI_INTR_VI
    c.step()
    assert c.cp0[CP0_EPC] == 0x80001000 and c.cp0[CP0_CAUSE] & CAUSE_BD
    assert (c.cp0[CP0_CAUSE] & 0x7C) == 0
    # TLB refill (no entry) → 0x80000000; BadVAddr/Context/EntryHi filled.
    t = fresh(); c = t.cpu
    put_be32(t.rdram, 0x1000, 0x3C080040)   # lui t0,0x0040
    put_be32(t.rdram, 0x1004, 0x8D090010)   # lw t1,0x10(t0)
    c.pc, c.next_pc = 0x80001000, 0x80001004
    c.cp0[CP0_ENTRYHI] = 0x00000005
    c.step(); c.step()
    assert c.pc == 0x80000000 and ((c.cp0[CP0_CAUSE] >> 2) & 0x1F) == 2
    assert c.cp0[CP0_BADVADDR] == 0x00400010 and c.cp0[CP0_EPC] == 0x80001004
    assert c.cp0[CP0_ENTRYHI] == 0x00400005 and (c.cp0[CP0_CONTEXT] & 0x7FFFF0) == (0x00400010 >> 9) & 0x7FFFF0
    # Map 16 KB pages: VA 0x00400000 even→PA 0x00100000, odd (0x00404000)→PA 0x00200000 (read-only).
    def map16k(c, idx, va, pa0, pa1, d0, d1, asid=0, g=1):
        c.cp0[CP0_PAGEMASK] = 0x00006000
        c.cp0[CP0_ENTRYHI] = (va & 0xFFFFE000) | asid
        c.cp0[CP0_ENTRYLO0] = ((pa0 >> 12) << 6) | (d0 << 2) | 2 | g
        c.cp0[CP0_ENTRYLO1] = ((pa1 >> 12) << 6) | (d1 << 2) | 2 | g
        c._write_tlb_entry(idx)
    map16k(c, 3, 0x00400000, 0x00100000, 0x00200000, 1, 0)
    put_be32(t.rdram, 0x00102344, 0xCAFEBABE); put_be32(t.rdram, 0x00203344, 0x0BADF00D)
    assert t.bus.read_u32(0x00402344) == 0xCAFEBABE and t.bus.read_u32(0x00407344) == 0x0BADF00D
    # TLBP honors the page mask; TLBR round-trips.
    c.cp0[CP0_ENTRYHI] = 0x00406000
    _h_TLBP(c, None, 0, c.gpr); assert c.cp0[CP0_INDEX] == 3
    c.cp0[CP0_INDEX] = 3; _h_TLBR(c, None, 0, c.gpr)
    assert c.cp0[CP0_PAGEMASK] == 0x00006000 and (c.cp0[CP0_ENTRYLO1] >> 6) == 0x200
    # Store to clean (D=0) page → TLB Mod (code 1) via general vector.
    c.cp0[CP0_STATUS] &= ~STATUS_EXL
    put_be32(t.rdram, 0x1008, 0x3C080040)   # lui t0,0x0040
    put_be32(t.rdram, 0x100C, 0xAD095000)   # sw t1,0x5000(t0) → 0x00405000 (odd page, D=0)
    c.pc, c.next_pc = 0x80001008, 0x8000100C
    c.step(); c.step()
    assert c.pc == 0x80000180 and ((c.cp0[CP0_CAUSE] >> 2) & 0x1F) == 1
    # Invalid entry (V=0) → TLBL via general vector, not refill.
    c.cp0[CP0_STATUS] &= ~STATUS_EXL
    c.cp0[CP0_PAGEMASK] = 0; c.cp0[CP0_ENTRYHI] = 0x00800000
    c.cp0[CP0_ENTRYLO0] = 1; c.cp0[CP0_ENTRYLO1] = 1; c._write_tlb_entry(4)
    try:
        t.bus.read_u32(0x00800000); assert False
    except TLBException as e:
        assert e.code == 2 and not e.refill
    # Scheduler: events fire in due order at the right times.
    t = fresh(); fired = []
    t._ev_PI = lambda: fired.append(("PI", t.now)); t._ev_SI = lambda: fired.append(("SI", t.now))
    t.schedule("PI", 300); t.schedule("SI", 100)
    t.cpu.cp0[CP0_COUNT] = 150; t._run_events()
    assert fired == [("SI", 150)]
    t.cpu.cp0[CP0_COUNT] = 400; t._run_events()
    assert [k for k, _ in fired] == ["SI", "PI"] and "PI" not in t.events
    # VI scanline advances with time and wraps at V_SYNC.
    t = fresh(); t.bus.regs[VI_V_SYNC] = 525; t.bus.regs[VI_INTR] = 2
    l0 = t.vi_current_line()
    t.cpu.cp0[CP0_COUNT] = t.vi_frame_len() // 2; l1 = t.vi_current_line()
    assert l0 == 2 and 250 <= l1 <= 270
    # COMPARE match with count_per_op=2 raises IP7 even when stepping over the exact value.
    t = fresh(); c = t.cpu
    put_be32(t.rdram, 0x1000, 0); c.pc, c.next_pc = 0x80001000, 0x80001004
    c.cp0[CP0_COUNT] = 100; c.cp0[CP0_COMPARE] = 101; c.cp0[CP0_CAUSE] = 0
    c.step(); assert c.cp0[CP0_CAUSE] & CAUSE_IP7
    # MI_MODE write bit 11 acks the DP interrupt; VI_CURRENT write acks VI.
    t.bus.hw_interrupts = MI_INTR_DP | MI_INTR_VI
    t.bus._write_mmio(MI_MODE, MI_CLR_DP_INTR); t.bus._write_mmio(VI_V_CURRENT, 0)
    assert t.bus.hw_interrupts == 0
    # ── Graphics: ucode detection, texel formats, rasterizer, combiner, Z, VI (US-009..US-017) ──
    assert classify_ucode_text("RSP Gfx ucode F3DEX       fifo 2.08  Yoshitaka Yasumoto 1999 Nintendo.") == UCODE_F3DEX2
    assert classify_ucode_text("RSP Gfx ucode F3DZEX.NoN  fifo 2.06H Yoshitaka Yasumoto 1998 Nintendo.") == UCODE_F3DEX2
    assert classify_ucode_text("RSP Gfx ucode F3DEX       1.23 Yoshitaka Yasumoto 1997 Nintendo.") == UCODE_F3DEX
    assert classify_ucode_text("RSP Gfx ucode F3DLX.Rej   1.21 Yoshitaka Yasumoto 1996 Nintendo.") == UCODE_F3DEX
    assert classify_ucode_text("RSP Gfx ucode S2DEX  1.07 Yoshitaka Yasumoto 1998 Nintendo.") == UCODE_S2DEX
    assert classify_ucode_text("RSP Gfx ucode S2DEX       fifo 2.05  Yoshitaka Yasumoto 1998 Nintendo.") == UCODE_S2DEX2
    assert classify_ucode_text("RSP SW Version: 2.0D, 04-01-96") == UCODE_F3D
    g = ACsN64Core(); g.lle = True; rd = g.rdram; rdp = g.rdp
    banner = b"RSP Gfx ucode F3DEX       fifo 2.08  Yoshitaka Yasumoto 1999 Nintendo."
    rd[0x10100:0x10100 + len(banner)] = banner
    assert detect_gfx_ucode(rd, 0x10000)[0] == UCODE_F3DEX2
    assert detect_gfx_ucode(rd, 0x20000) == ("", "")
    # Texel formats: one texel per format through TMEM.
    def tile(ti, fmt, siz, line=1, tmem=0, pal=0, w=4, h=4):
        rdp.set_tile((0xF5 << 24) | (fmt << 21) | (siz << 19) | (line << 9) | tmem, (ti << 24) | (pal << 20))
        rdp.set_tile_size(0, (ti << 24) | (((w - 1) << 2) << 12) | ((h - 1) << 2))
        rdp._touch_tmem()
        return rdp._decode_tile(ti)[0]
    tm = rdp.tmem
    tm[0:2] = b"\xF8\x01"                                    # RGBA16 red, alpha 1
    assert tile(0, G_IM_FMT_RGBA, G_IM_SIZ_16b)[0] == (255, 0, 0, 255)
    tm[0:2] = b"\x12\x34"; tm[0x800:0x802] = b"\x56\x78"   # RGBA32 split across halves
    assert tile(0, G_IM_FMT_RGBA, G_IM_SIZ_32b)[0] == (0x12, 0x34, 0x56, 0x78)
    tm[0] = 0x9F                                              # IA8: I=9, A=F
    assert tile(0, G_IM_FMT_IA, G_IM_SIZ_8b)[0] == (153, 153, 153, 255)
    tm[0:2] = b"\x80\x40"                                    # IA16
    assert tile(0, G_IM_FMT_IA, G_IM_SIZ_16b)[0] == (0x80, 0x80, 0x80, 0x40)
    tm[0] = 0xF3                                              # IA4: texel0 = 0xF → I=7 A=1
    assert tile(0, G_IM_FMT_IA, G_IM_SIZ_4b)[0] == (255, 255, 255, 255)
    tm[0] = 0x5A                                              # I4: texel0 = 5, texel1 = A
    i4 = tile(0, G_IM_FMT_I, G_IM_SIZ_4b)
    assert i4[0] == (85, 85, 85, 85) and i4[1] == (170, 170, 170, 170)
    tm[0] = 0x42
    assert tile(0, G_IM_FMT_I, G_IM_SIZ_8b)[0] == (0x42, 0x42, 0x42, 0x42)
    rdp.omh = 2 << 14                                         # TLUT RGBA16
    tm[0] = 0x03; tm[0x800 + 3 * 8:0x800 + 3 * 8 + 2] = b"\x07\xC1"   # CI8 index 3 → green
    assert tile(0, G_IM_FMT_CI, G_IM_SIZ_8b)[0] == (0, 255, 0, 255)
    tm[0] = 0x20; tm[0x800 + (16 + 2) * 8:0x800 + (16 + 2) * 8 + 2] = b"\x00\x3F"  # CI4 pal 1, idx 2 → blue
    assert tile(0, G_IM_FMT_CI, G_IM_SIZ_4b, pal=1)[0] == (0, 0, 255, 255)
    rdp.omh = 0
    # LoadBlock / LoadTile / LoadTLUT from a texture image in RDRAM.
    for k in range(16):
        put_be16 = lambda o, v: rd.__setitem__(slice(o, o + 2), bytes(((v >> 8) & 255, v & 255)))
        put_be16(0x20000 + k * 2, 0xF801 if k % 2 == 0 else 0x07C1)
    rdp.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, 4, 0x20000)
    rdp.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (1 << 9), 7 << 24)
    rdp.load_block(0, (7 << 24) | (15 << 12) | 0x800)  # dxt = 1 line per 8 bytes
    blk = tile(0, G_IM_FMT_RGBA, G_IM_SIZ_16b)
    assert blk[0] == (255, 0, 0, 255) and blk[1] == (0, 255, 0, 255) and blk[4] == (255, 0, 0, 255)
    rdp.load_tile(0, (7 << 24) | (12 << 12) | 12)        # 4x4 rectangle, rows swapped on odd lines
    lt = tile(0, G_IM_FMT_RGBA, G_IM_SIZ_16b)
    assert lt == blk
    rdp.set_tile((1 << 9) | 0x100, 6 << 24)               # TLUT at TMEM 0x800
    rdp.load_tlut(0, (6 << 24) | (3 << 2 << 12))
    assert bytes(tm[0x800:0x808]) == b"\xF8\x01" * 4 and bytes(tm[0x808:0x80A]) == b"\x07\xC1"
    # Sampler wrap / mirror / clamp and bilinear.
    for k in range(16):
        tm[k * 2:k * 2 + 2] = bytes((k * 8, 1))
    rdp.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (1 << 9), (1 << 24) | (2 << 14) | (2 << 4))
    rdp.set_tile_size(0, (1 << 24) | (12 << 12) | 12); rdp._touch_tmem()
    smp = rdp._sampler(1, False)
    assert smp(5.0, 0.0) == smp(1.0, 0.0)                 # wrap with mask 2
    rdp.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (1 << 9), (1 << 24) | (2 << 14) | (1 << 8) | (2 << 4))
    rdp._touch_tmem(); smp = rdp._sampler(1, False)
    assert smp(4.0, 0.0) == smp(3.0, 0.0) and smp(5.0, 0.0) == smp(2.0, 0.0)  # mirror
    rdp.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (1 << 9), (1 << 24) | (2 << 8))
    rdp._touch_tmem(); smp = rdp._sampler(1, False)
    assert smp(9.0, 0.0) == smp(3.0, 0.0) and smp(-3.0, 0.0) == smp(0.0, 0.0)  # clamp
    bl = rdp._sampler(1, True)
    # RDP bilinear: integer s hits a texel exactly; s = 0.5 is halfway between texels 0 and 1.
    assert bl(1.0, 0.0) == smp(1.0, 0.0)
    mid = bl(0.5, 0.0)
    assert mid[0] == (smp(0.0, 0.0)[0] + smp(1.0, 0.0)[0]) // 2
    # Textured triangle (1-cycle, combiner = TEXEL0) into a 16-bit framebuffer.
    rdp.reset()
    rdp.set_color_image(0, G_IM_SIZ_16b, 32, 0x100000)
    rdp.scissor = (0, 0, 32, 32)
    rd[0x20000:0x20020] = bytes(32)
    for k in range(16):
        v = 0xF801 if (k % 4) < 2 else 0x003F
        rd[0x20000 + k * 2:0x20002 + k * 2] = bytes(((v >> 8) & 255, v & 255))
    rdp.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, 4, 0x20000)
    rdp.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (1 << 9), 0)
    rdp.load_tile(0, (12 << 12) | 12)
    rdp.set_tile_size(0, (12 << 12) | 12)
    rdp.omh = G_CYC_1CYCLE << 20
    # (0-0)*0+TEXEL0 for RGB and alpha: a=15,c=31? use explicit D=1 selectors.
    rdp.combine = ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31,
                   (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (1 << 15) | (7 << 12) | (1 << 9) | (1 << 6) | (7 << 3) | 1)
    v = lambda x, y, s_, t_: (x, y, 0.0, 1.0, s_, t_, 0.0, 0.0, 0.0, 255.0)
    rdp.draw_triangle(v(0, 0, 0, 0), v(16, 0, 4, 0), v(0, 16, 0, 4), 0, True)
    px = lambda x, y: (rd[0x100000 + (y * 32 + x) * 2] << 8) | rd[0x100000 + (y * 32 + x) * 2 + 1]
    assert px(1, 1) == 0xF801 and px(9, 1) == 0x003F and px(15, 15) == 0  # texels, outside untouched
    # Combiner: (SHADE - 0) * PRIM + 0, flat colour.
    rdp.prim = (128, 128, 128, 255)
    rdp.combine = ((4 << 20) | (3 << 15) | (7 << 12) | (7 << 9) | (4 << 5) | 3,
                   (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (7 << 15) | (7 << 12) | (6 << 9) | (7 << 6) | (7 << 3) | 6)
    sh = lambda x, y: (x, y, 0.0, 1.0, 0.0, 0.0, 255.0, 0.0, 0.0, 255.0)
    rdp.draw_triangle(sh(20, 0), sh(32, 0), sh(20, 12), 0, False)
    assert (px(21, 1) >> 11) == ((255 * 128 // 256) >> 3)
    # Blender: force_bl alpha blend (CLR_IN*IN_A + CLR_MEM*(1-A)) at 50% over white.
    rd[0x100000 + (1 * 32 + 21) * 2:0x100000 + (1 * 32 + 21) * 2 + 2] = b"\xFF\xFF"
    rdp.combine = ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31,
                   (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (4 << 15) | (7 << 12) | (4 << 9) | (4 << 6) | (7 << 3) | 4)
    rdp.oml = RM_FORCE_BL | RM_IM_RD | (0 << 30) | (0 << 26) | (1 << 22) | (0 << 18)
    half = lambda x, y: (x, y, 0.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 128.0)
    rdp.draw_triangle(half(20, 0), half(26, 0), half(20, 6), 0, False)
    assert 14 <= (px(21, 1) >> 11) <= 17  # ~half of white over black
    # Z-buffer: nearer triangle wins regardless of draw order.
    rdp.oml = RM_Z_CMP | RM_Z_UPD; rdp.zimg = 0x110000
    rd[0x110000:0x110000 + 32 * 32 * 2] = b"\xFF\xFC" * (32 * 32)
    rdp.combine = ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31,
                   (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (4 << 15) | (7 << 12) | (4 << 9) | (4 << 6) | (7 << 3) | 4)
    zc = lambda x, y, z, r, b_: (x, y, z, 1.0, 0.0, 0.0, r, 0.0, b_, 255.0)
    for order in ((1000.0, 255.0, 0.0, 9000.0, 0.0, 255.0), (9000.0, 0.0, 255.0, 1000.0, 255.0, 0.0)):
        rd[0x110000:0x110000 + 32 * 32 * 2] = b"\xFF\xFC" * (32 * 32)
        za, ra, ba, zb, rb, bb = order
        rdp.draw_triangle(zc(0, 20, za, ra, ba), zc(12, 20, za, ra, ba), zc(0, 32, za, ra, ba), 0, False)
        rdp.draw_triangle(zc(0, 20, zb, rb, bb), zc(12, 20, zb, rb, bb), zc(0, 32, zb, rb, bb), 0, False)
        assert (px(2, 22) >> 11) == 31 and ((px(2, 22) >> 1) & 31) == 0  # red (near, z=1000) wins
    assert z_decompress(z_compress(0x3F000)) == 0x3F000 and z_compress(0x100) < z_compress(0x30000)
    # Fill mode rectangle writes the 32-bit fill colour pair.
    rdp.omh = G_CYC_FILL << 20; rdp.fill_color = 0xF801F801
    rdp.fill_rect(0, 30 << 2, 3 << 2, 31 << 2)
    assert px(0, 30) == 0xF801 and px(3, 31) == 0xF801
    # F3D and F3DEX2 display lists: matrices, viewport, VTX, TRI, nested DL, segments, CULLDL.
    def dl_test(fam):
        t = ACsN64Core(); t.lle = True; m = t.rdram
        put = lambda o, w: put_be32(m, o, w)
        ident = [0x00010000, 0, 0x00000001, 0, 0, 0x00010000, 0, 0x00000001] + [0] * 8
        for k, w in enumerate(ident): put(0x3000 + k * 4, w)
        struct.pack_into(">8h", m, 0x3100, 640, 480, 511, 0, 640, 480, 511, 0)
        for k, (x, y) in enumerate(((-0.5, -0.5), (0.5, -0.5), (-0.5, 0.5), (0.5, 0.5))):
            struct.pack_into(">hhhhhhBBBB", m, 0x3200 + k * 16, int(x * 1), int(y * 1), 0, 0, 0, 0, 255, 255, 255, 255)
        # Scale vertices into view with a projection that maps ±1 → ±1 (identity) and x0.5 coords.
        struct.pack_into(">hhhhhhBBBB", m, 0x3200, -1, -1, 0, 0, 0, 0, 255, 255, 255, 255)
        struct.pack_into(">hhhhhhBBBB", m, 0x3210, 1, -1, 0, 0, 0, 0, 255, 255, 255, 255)
        struct.pack_into(">hhhhhhBBBB", m, 0x3220, -1, 1, 0, 0, 0, 0, 255, 255, 255, 255)
        cmds = []
        if fam == UCODE_F3D:
            cmds = [(0xBC001806, 0x00000000),               # segment 6 = 0
                    (0x01030040, 0x06003000), (0x01000040, 0x06003000),   # proj load, mv load
                    (0x03800010, 0x06003100),               # viewport
                    (0xB7000000, 0x00000004),               # shade
                    (0xFF10013F, 0x00100000),               # color image 16-bit, width 320
                    (0xBA001402, 0x00000000),               # cycle type 1cyc
                    (0xFC000000 | ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31),
                     (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (4 << 15) | (7 << 12) | (4 << 9) | (4 << 6) | (7 << 3) | 4),
                    (0x06000000, 0x00003400),               # call nested DL
                    (0xB8000000, 0)]
            nested = [(0x04200030, 0x00003200), (0xBF000000, 0x00000A14), (0xB8000000, 0)]
        else:
            cmds = [(0xDB060018, 0x00000000),
                    (0xDA380005, 0x00003000),               # proj load nopush
                    (0xDA380003, 0x00003000),               # mv load nopush
                    (0xDC080008, 0x00003100),
                    (0xD9FFFFFF, 0x00000004),
                    (0xFF10013F, 0x00100000),
                    (0xE3001401, 0x00000000),
                    (0xFC000000 | ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31),
                     (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (4 << 15) | (7 << 12) | (4 << 9) | (4 << 6) | (7 << 3) | 4),
                    (0xDE000000, 0x00003400),
                    (0xDF000000, 0)]
            nested = [(0x01003006, 0x00003200), (0x05000204, 0), (0x03000000, 0x00000004), (0x05000204, 0), (0xDF000000, 0)]
        for k, (w0, w1) in enumerate(cmds): put(0x4000 + k * 8, w0); put(0x4004 + k * 8, w1)
        for k, (w0, w1) in enumerate(nested): put(0x3400 + k * 8, w0); put(0x3404 + k * 8, w1)
        t.gfx.run_task(0x4000, fam)
        return t
    t3 = dl_test(UCODE_F3D)
    assert t3.rdp.stats["tris"] == 1 and t3.rdp.stats["pixels"] > 1000, t3.rdp.stats
    assert be32(t3.rdram, 0x100000 + (120 * 320 + 160) * 2) >> 16 != 0
    t2 = dl_test(UCODE_F3DEX2)
    assert t2.rdp.stats["tris"] == 2, t2.rdp.stats  # on-screen verts: CULLDL falls through
    for k in range(3): t2.gfx.verts[k].clip = 2       # all right of the frustum
    assert t2.gfx.cull_dl(0, 2)
    t2.gfx.verts[1].clip = 0
    assert not t2.gfx.cull_dl(0, 2)
    t2.gfx.run_task(0x5000, UCODE_F3DEX2)  # empty memory = NOOPs until runaway guard / zero op
    put_be32(t2.rdram, 0x6000, 0xAB000000); put_be32(t2.rdram, 0x6008, 0xDF000000)
    t2.gfx.run_task(0x6000, UCODE_F3DEX2)
    assert "gfx:f3dex2:AB" in t2.unimpl
    # VI scan-out: 16-bit and 32-bit, blanking, numpy and pure paths agree.
    vt = ACsN64Core(); vt.lle = True
    rg = vt.bus.regs
    rg.update({VI_STATUS: 0x3016 | 2, VI_WIDTH: 320, VI_H_START: (0x6C << 16) | 0x2EC,
               VI_V_START: (0x25 << 16) | 0x1FF, VI_X_SCALE: 0x200, VI_Y_SCALE: 0x400, VI_ORIGIN: 0x200000})
    assert vt.vi_geometry() == (320, 320, 237, 2)
    vt.rdram[0x200000:0x200002] = b"\xF8\x01"
    vt.render_vi()
    hdr = b"P6\n320 237\n255\n"
    assert vt.fb_ppm.startswith(hdr) and vt.fb_ppm[len(hdr):len(hdr) + 3] == b"\xFF\x00\x00"
    if _np is not None:
        assert vi_frame_to_ppm(vt.rdram, 0x200000, 320, 320, 237, 2, True) == vi_frame_to_ppm(vt.rdram, 0x200000, 320, 320, 237, 2, False)
    rg[VI_STATUS] = 0x3016 | 3
    vt.rdram[0x200000:0x200004] = b"\x10\x20\x30\xFF"
    assert vt.vi_geometry()[3] == 4
    vt.render_vi(); assert vt.fb_ppm[len(hdr):len(hdr) + 3] == b"\x10\x20\x30"
    if _np is not None:
        assert vi_frame_to_ppm(vt.rdram, 0x200000, 320, 320, 237, 4, True) == vi_frame_to_ppm(vt.rdram, 0x200000, 320, 320, 237, 4, False)
    rg[VI_H_START] = 0  # osViBlack
    assert vt.vi_geometry() is None
    vt.render_vi(); assert ppm_brightness(vt.fb_ppm) == 0.0
    # Interlaced hi-res: Y scale 0x800 doubles the source lines.
    rg.update({VI_H_START: (0x6C << 16) | 0x2EC, VI_WIDTH: 640, VI_X_SCALE: 0x400, VI_Y_SCALE: 0x800, VI_STATUS: 0x3056 | 2})
    assert vt.vi_geometry() == (640, 640, 474, 2)
    _selftest_jit_fpu()
    _selftest_frameskip()
    # ── Joybus controllers, paks, EEPROM (US-018 / US-021) ──
    j = ACsN64Core(); j.lle = True
    j.pad_connected[:] = [True, False, False, False]
    j.set_pad(0, PAD_BUTTONS["A"] | PAD_BUTTONS["START"], 80, -80)
    blk = bytearray(PIF_RAM_SIZE)
    # libultra osContStartReadData layout: per channel {0xFF pad, tx=1, rx=4, cmd 0x01, 4 resp bytes}.
    blk[0:8] = bytes((0xFF, 0x01, 0x04, 0x01, 0xFF, 0xFF, 0xFF, 0xFF))
    blk[8:16] = bytes((0xFF, 0x01, 0x04, 0x01, 0xFF, 0xFF, 0xFF, 0xFF))
    blk[16] = 0xFE
    j.pif_ram[:] = blk
    j._pif_process_commands()
    assert bytes(j.pif_ram[4:8]) == bytes((0x90, 0x00, 80, 0xB0))      # A|START, x=80, y=-80
    assert j.pif_ram[10] & 0x80                                         # port 2 unplugged
    # Status (cmd 0x00): standard controller, no pak → 0x05 0x00 0x02.
    j.pif_ram[:] = bytes((0xFF, 0x01, 0x03, 0x00, 0xFF, 0xFF, 0xFF, 0xFE)) + bytes(PIF_RAM_SIZE - 8)
    j._pif_process_commands()
    assert bytes(j.pif_ram[4:7]) == b"\x05\x00\x02"
    # Controller Pak write → read round-trip with libultra CRCs.
    j.pad_paks[0] = PAK_MEMPAK
    payload = bytes(range(32))
    addr = 0x0040
    ah = (addr | pak_address_crc(addr >> 5)) & 0xFFFF
    wr = bytes((0x23, 0x01, 0x03, ah >> 8, ah & 0xFF)) + payload + bytes((0xFF,))
    j.pif_ram[:] = (wr + b"\xFE").ljust(PIF_RAM_SIZE, b"\0")
    j._pif_process_commands()
    assert j.pif_ram[5 + 32] == pak_data_crc(payload) and j.mempaks[0][0x40:0x60] == payload
    rdq = bytes((0x03, 0x21, 0x02, ah >> 8, ah & 0xFF)) + bytes(33)
    j.pif_ram[:] = (rdq + b"\xFE").ljust(PIF_RAM_SIZE, b"\0")
    j._pif_process_commands()
    assert bytes(j.pif_ram[5:37]) == payload and j.pif_ram[37] == pak_data_crc(payload)
    assert pak_data_crc(bytes(32)) != pak_data_crc(payload) and 0 <= pak_address_crc(0x7FF) < 32
    # Rumble Pak: probe 0x8000 with 0x80 → reads back 0x80; 0xC000 drives the motor.
    j.pad_paks[0] = PAK_RUMBLE
    j._pak_write(0, 0x8000, b"\x80" * 32); assert j._pak_read(0, 0x8000) == b"\x80" * 32
    j._pak_write(0, 0xC000, b"\x01" * 32); assert j.rumble_state[0]
    j._pak_write(0, 0xC000, b"\x00" * 32); assert not j.rumble_state[0]
    # EEPROM over Joybus channel 4: status, write, read.
    j.save_mgr.save_type = SAVE_EEPROM_4K
    j.pif_ram[:] = (bytes((0, 0, 0, 0, 0x0A, 0x01, 0x05, 0x02)) + b"ABCDEFGH" + b"\xFF\xFE").ljust(PIF_RAM_SIZE, b"\0")
    j._pif_process_commands()
    j.pif_ram[:] = (bytes((0, 0, 0, 0, 0x02, 0x08, 0x04, 0x02)) + bytes(8) + b"\xFE").ljust(PIF_RAM_SIZE, b"\0")
    j._pif_process_commands()
    assert bytes(j.pif_ram[8:16]) == b"ABCDEFGH"
    # Keyboard map → pad bits / stick.
    bits, x, y = pad_from_keys(DEFAULT_KEYMAP, {"x", "Up", "Return"})
    assert bits == PAD_BUTTONS["A"] | PAD_BUTTONS["START"] and (x, y) == (0, STICK_RANGE)
    # ── Save persistence: EEPROM / SRAM / FlashRAM / Controller Pak (US-019 / US-020) ──
    import tempfile
    # UI prefs: Show Rom List persists off/on (cathle_ui.json).
    with tempfile.TemporaryDirectory() as td:
        up = os.path.join(td, "ui.json")
        save_ui_prefs({"show_rom_list": False}, up)
        assert load_ui_prefs(up)["show_rom_list"] is False
        save_ui_prefs({"show_rom_list": True}, up)
        assert load_ui_prefs(up)["show_rom_list"] is True
        save_ui_prefs({"show_rom_list": True, "frameskip": "auto"}, up)
        assert load_ui_prefs(up)["frameskip"] == "auto" and normalize_frameskip("bogus") == "off"
        assert load_ui_prefs(os.path.join(td, "missing.json"))["show_rom_list"] is True
    with tempfile.TemporaryDirectory() as td:
        def save_core(save_type):
            t = ACsN64Core(); t.save_dir = td
            t.rom_header = N64Header(boot_rom); t.save_mgr.save_type = save_type
            t.load_saves()
            return t
        t = save_core(SAVE_EEPROM_4K)
        t.save_mgr.eeprom_write_block(3, b"SAVEDATA")
        assert t.flush_saves() and not t.save_mgr.dirty
        t2 = save_core(SAVE_EEPROM_4K)
        assert bytes(t2.save_mgr.eeprom[24:32]) == b"SAVEDATA"
        # SRAM via PI DMA (cart domain 2 at 0x08000000) and direct CPU word access.
        t = save_core(SAVE_SRAM)
        t.rdram[0x1000:0x1010] = b"0123456789ABCDEF"
        t.save_mgr.pi_write(0x08000100, 16, t.rdram, 0x1000)
        t.save_mgr.pi_read(0x08000100, 16, t.rdram, 0x2000)
        assert bytes(t.rdram[0x2000:0x2010]) == b"0123456789ABCDEF"
        t.bus.write_u32(0xA8000200, 0xDEADBEEF)
        assert t.bus.read_u32(0xA8000200) == 0xDEADBEEF
        t.flush_saves()
        assert bytes(save_core(SAVE_SRAM).save_mgr.sram[0x100:0x110]) == b"0123456789ABCDEF"
        # FlashRAM: silicon ID, sector erase, page program, array read (half-addressed), persistence.
        t = save_core(SAVE_FLASHRAM); fm = t.save_mgr
        t.bus.write_u32(0xA8010000, 0xE1000000)            # status mode
        t.save_mgr.pi_read(0x08000000, 8, t.rdram, 0x3000)
        assert be32(t.rdram, 0x3000) == 0x11118001 and be32(t.rdram, 0x3004) == 0x00C20000
        fm.flashram[0:4] = b"\x00\x00\x00\x00"
        t.bus.write_u32(0xA8010000, 0x4B000000); t.bus.write_u32(0xA8010000, 0xD2000000)  # erase sector 0
        assert bytes(fm.flashram[0:4]) == b"\xFF\xFF\xFF\xFF"
        t.rdram[0x4000:0x4080] = bytes(range(128))
        t.bus.write_u32(0xA8010000, 0xB4000000)            # write mode
        t.save_mgr.pi_write(0x08000000, 128, t.rdram, 0x4000)
        t.bus.write_u32(0xA8010000, 0xA5000002)            # program page 2 (offset 0x100)
        t.bus.write_u32(0xA8010000, 0xD2000000)
        assert bytes(fm.flashram[0x100:0x180]) == bytes(range(128))
        t.bus.write_u32(0xA8010000, 0xF0000000)            # read array mode
        t.save_mgr.pi_read(0x08000080, 128, t.rdram, 0x5000)   # 0x80 * 2 = 0x100
        assert bytes(t.rdram[0x5000:0x5080]) == bytes(range(128))
        t.flush_saves()
        assert bytes(save_core(SAVE_FLASHRAM).save_mgr.flashram[0x100:0x180]) == bytes(range(128))
        # Controller Pak persists per port.
        t = save_core(SAVE_EEPROM_4K); t.pad_paks[1] = PAK_MEMPAK
        t._pak_write(1, 0x20, b"P" * 32); assert t.flush_saves()
        t3 = save_core(SAVE_EEPROM_4K)
        assert bytes(t3.mempaks[1][0x20:0x40]) == b"P" * 32
        saved = os.listdir(td)
        assert any(n.endswith(".eep") for n in saved) and any(n.endswith(".sra") for n in saved)
        assert any(n.endswith(".fla") for n in saved) and any(n.endswith(".p2.mpk") for n in saved)
    # Harness cores never touch disk.
    assert ACsN64Core().save_dir is not None
    # ── HLE audio ABI1 primitives (US-022) ──
    au = ACsN64Core().audio
    assert all(abs(sum(RESAMPLE_LUT[k * 4:k * 4 + 4]) - 32768) <= 2 for k in range(64))
    # ADPCM with a zero codebook reproduces the scaled nibbles; state is written back.
    au.table = [0] * 128
    au.buf[0x100] = 0xC0                       # scale 12 (no shift), codebook entry 0
    au.buf[0x101:0x109] = bytes([0x12, 0x3F, 0x70, 0x08, 0, 0, 0, 0x7F])
    au.adpcm(True, False, 0x200, 0x100, 32, 0x30000)
    dec = [au.rs16(0x220 + k * 2) for k in range(16)]
    assert dec[:4] == [0x1000, 0x2000, 0x3000, -0x1000] and dec[15] == -0x1000
    assert ACsN64Core().audio is not None and au._dram_s16(0x30000 + 15 * 2) == -0x1000
    # Mixer: dst += src * gain (Q15).
    au.count = 32
    for k in range(16): au.ws16(ABI1_DMEM_BASE + 0x40 + k * 2, 1000); au.ws16(ABI1_DMEM_BASE + k * 2, 100)
    au._mixer(0x0C007FFF, (0x40 << 16) | 0x00)
    assert au.rs16(ABI1_DMEM_BASE) == 100 + ((1000 * 0x7FFF + 0x4000) >> 15)  # rounded like the ucode
    # Interleave: L/R sample pairs.
    au.count = 16
    for k in range(8): au.ws16(ABI1_DMEM_BASE + 0x100 + k * 2, k); au.ws16(ABI1_DMEM_BASE + 0x200 + k * 2, -k)
    au.out = 0x900
    au._interleave(0x0D000000, (0x100 << 16) | 0x200)
    assert [au.rs16(0x900 + k * 2) for k in range(6)] == [0, 0, 1, -1, 2, -2]
    # Envelope mixer: unity volume/target passes the input through to both dry channels.
    au.count = 32; au.in_ = 0x300; au.out = 0x400; au.dry_right = 0x500
    au.buf[0x400:0x440] = bytes(64); au.buf[0x500:0x540] = bytes(64)
    for k in range(16): au.ws16(0x300 + k * 2, 8000)
    au.vol = [0x7FFF, 0x7FFF]; au.target = [0x7FFF, 0x7FFF]; au.rate = [0x10000, 0x10000]
    au.dry = 0x7FFF; au.wet = 0
    au.envmix_exp(True, False, 0x31000)
    assert 7980 <= au.rs16(0x400) <= 8000 and 7980 <= au.rs16(0x500 + 30) <= 8000
    # Resample at pitch 1.0 keeps a DC signal's level.
    for k in range(64): au.ws16(0x600 + k * 2, 10000)
    for k in range(4): au._dram_w16(0x32000 + k * 2, 10000)
    au._dram_w16(0x32008, 0)
    au.resample(False, 0x700, 0x600, 32, 0x10000, 0x32000)
    assert all(abs(au.rs16(0x700 + k * 2) - 10000) <= 3 for k in range(16))
    # Signed division truncates toward zero (MIPS), divide-by-zero results stay 64-bit.
    dv = ACsN64Core().cpu
    dv.gpr[4] = u64(-7); dv.gpr[5] = 2
    _h_DIV(dv, N64Opcode(0x0085001A), 0, dv.gpr)
    assert sign64(dv.lo) == -3 and sign64(dv.hi) == -1
    _h_DDIV(dv, N64Opcode(0x0085001E), 0, dv.gpr)
    assert sign64(dv.lo) == -3 and sign64(dv.hi) == -1
    dv.gpr[5] = 0
    _h_DIVU(dv, N64Opcode(0x0085001B), 0, dv.gpr); assert dv.lo == MASK_64
    _h_DIV(dv, N64Opcode(0x0085001A), 0, dv.gpr); assert dv.lo == 1 and 0 <= dv.hi <= MASK_64
    # numpy texture decode matches the pure-Python decoder for every format (US-024).
    if _np is not None:
        rt = ACsN64Core().rdp
        rnd = random.Random(1234)
        rt.tmem[:] = bytes(rnd.randrange(256) for _ in range(4096))
        global USE_NUMPY
        saved_np = USE_NUMPY
        try:
            for fmt, siz, tl in ((0, 2, 0), (0, 3, 0), (2, 1, 2), (2, 0, 2), (2, 1, 3), (3, 0, 0), (3, 1, 0),
                                 (3, 2, 0), (4, 0, 0), (4, 1, 0), (0, 1, 2), (2, 2, 2)):
                rt.omh = tl << 14
                rt.set_tile((fmt << 21) | (siz << 19) | (3 << 9) | 0x20, (2 << 24) | (3 << 20))
                rt.set_tile_size(0, (2 << 24) | ((15 << 2) << 12) | (7 << 2))
                USE_NUMPY = False; rt._tex_cache.clear(); pure = rt._decode_tile(2)
                USE_NUMPY = True; rt._tex_cache.clear(); fast = rt._decode_tile(2)
                assert pure == fast, (fmt, siz, tl)
        finally:
            USE_NUMPY = saved_np
    # Save states: snapshot → mutate → restore gives back identical machine state (US-044).
    ss = fresh()
    ss.rom_header = N64Header(boot_rom)
    put_be32(ss.rdram, 0x1000, 0x24420001)  # addiu v0,v0,1
    put_be32(ss.rdram, 0x1004, 0x1000FFFE)  # b -2
    put_be32(ss.rdram, 0x1008, 0)
    ss.cpu.pc, ss.cpu.next_pc = 0x80001000, 0x80001004
    for _ in range(9): ss.cpu.step()
    ss.gfx.segments[3] = 0x123456; ss.rdp.tmem[5] = 0x77; ss.save_mgr.eeprom[0] = 0x42
    blob = ss.save_state()
    before = (list(ss.cpu.gpr), ss.cpu.pc, bytes(ss.rdram[:0x2000]), ss.gfx.segments[3], ss.rdp.tmem[5])
    for _ in range(7): ss.cpu.step()
    ss.gfx.segments[3] = 0; ss.rdp.tmem[5] = 0; ss.save_mgr.eeprom[0] = 0
    assert ss.load_state(blob) is None
    assert (list(ss.cpu.gpr), ss.cpu.pc, bytes(ss.rdram[:0x2000]), ss.gfx.segments[3], ss.rdp.tmem[5]) == before
    assert ss.save_mgr.eeprom[0] == 0x42
    other = fresh(); other.rom_header = N64Header(bytes(boot_rom[:0x10]) + b"\x11" * 8 + bytes(boot_rom[0x18:0x40]))
    assert other.load_state(blob) == "state belongs to a different ROM"
    # ── S2DEX: BG_COPY with scroll/wrap, OBJ_LOADTXTR + OBJ_RECTANGLE, OBJ_SPRITE (US-016) ──
    sd = ACsN64Core(); sd.lle = True; mm = sd.rdram
    banner = b"RSP Gfx ucode S2DEX  1.07 Yoshitaka Yasumoto 1998 Nintendo."
    mm[0x8100:0x8100 + len(banner)] = banner
    assert detect_gfx_ucode(mm, 0x8000)[0] == UCODE_S2DEX
    # 32x4 RGBA16 image: texel value encodes its column (r = col).
    for yy in range(4):
        for xx in range(32):
            mm[0x9000 + (yy * 32 + xx) * 2:0x9002 + (yy * 32 + xx) * 2] = bytes((((xx & 31) << 3), 1))
    # uObjBg: imageX=24 (u10.5), imageW=32 (u10.2), frameX=0, frameW=16, imageY=0, imageH=4, frameY=0, frameH=4
    struct.pack_into(">HHhHHHhHIHBBHH", mm, 0xA000, 24 << 5, 32 << 2, 0, 16 << 2, 0, 4 << 2, 0, 4 << 2,
                     0x9000, 0, G_IM_FMT_RGBA, G_IM_SIZ_16b, 0, 0)
    dl = [(0xFF10003F, 0x00100000),               # color image 16-bit width 64
          (0xBA001402, G_CYC_COPY << 20),          # copy mode
          (0xB9000002, 0),                         # no alpha compare
          (0x02000000, 0x0000A000),                # BG_COPY
          (0xB8000000, 0)]
    for k, (w0, w1) in enumerate(dl): put_be32(mm, 0xB000 + k * 8, w0); put_be32(mm, 0xB004 + k * 8, w1)
    sd.gfx.run_task(0xB000, UCODE_S2DEX)
    col = lambda x, y: mm[0x100000 + (y * 64 + x) * 2] >> 3
    assert [col(x, 1) for x in range(10)] == [24, 25, 26, 27, 28, 29, 30, 31, 0, 1], [col(x, 1) for x in range(10)]
    # OBJ_LOADTXTR (block) a 4x4 texture into TMEM, then OBJ_RECTANGLE at 2x zoom (scaleW=512).
    for k in range(16):
        mm[0x9800 + k * 2:0x9802 + k * 2] = bytes(((k << 3) & 0xFF, 1))
    struct.pack_into(">IIHHHHII", mm, 0xA100, 0x00001033, 0x9800, 0, (16 >> 2) - 1, 0x800, 0, 0, 0)
    # uObjSprite: objX=8<<2, scaleW=512, imageW=4<<5, objY=8<<2, scaleH=512, imageH=4<<5, stride=1, adrs=0
    struct.pack_into(">hHHHhHHHHHBBBB", mm, 0xA200, 8 << 2, 512, 4 << 5, 0, 8 << 2, 512, 4 << 5, 0, 1, 0,
                     G_IM_FMT_RGBA, G_IM_SIZ_16b, 0, 0)
    dl = [(0xBA001402, G_CYC_1CYCLE << 20),
          (0xFC000000 | ((15 << 20) | (31 << 15) | (7 << 12) | (7 << 9) | (15 << 5) | 31),
           (15 << 28) | (15 << 24) | (7 << 21) | (7 << 18) | (1 << 15) | (7 << 12) | (1 << 9) | (1 << 6) | (7 << 3) | 1),
          (0xC1000000, 0x0000A100), (0x03000000, 0x0000A200), (0xB8000000, 0)]
    for k, (w0, w1) in enumerate(dl): put_be32(mm, 0xB100 + k * 8, w0); put_be32(mm, 0xB104 + k * 8, w1)
    sd.gfx.run_task(0xB100, UCODE_S2DEX)
    # 2x zoom: screen (8,8),(9,8) → texel 0; (10,8) → texel 1; (8,10) → texel 4.
    assert col(8, 8) == 0 and col(9, 8) == 0 and col(10, 8) == 1 and col(8, 10) == 4 and col(15, 15) == 15
    # OBJ_MOVEMEM (identity matrix, offset 32,0) + OBJ_SPRITE draws two triangles.
    struct.pack_into(">iiiihhHH", mm, 0xA300, 0x10000, 0, 0, 0x10000, 32 << 2, 0, 1024, 1024)
    tris0 = sd.rdp.stats["tris"]
    dl = [(0x05000017, 0x0000A300), (0x04000000, 0x0000A200), (0xB8000000, 0)]
    for k, (w0, w1) in enumerate(dl): put_be32(mm, 0xB200 + k * 8, w0); put_be32(mm, 0xB204 + k * 8, w1)
    sd.gfx.run_task(0xB200, UCODE_S2DEX)
    assert sd.rdp.stats["tris"] == tris0 + 2
    # Expansion Pak: osMemSize reports 8 MB by default, 4 MB when disabled (US-026).
    xp = ACsN64Core(); xp.rom = boot_rom; xp.rom_header = N64Header(boot_rom)
    xp._hle_ipl3_boot(); assert be32(xp.rdram, 0x318) == 0x800000
    xp.ram_mb = 4; xp._hle_ipl3_boot(); assert be32(xp.rdram, 0x318) == 0x400000
    # ── LLE RSP: scalar unit, delay slots, BREAK, vector ops, vector load/store (US-027/US-028) ──
    rc = ACsN64Core(); rc.lle = True; rs_ = rc.rsp
    im = rc.rsp_imem; dm = rc.rsp_dmem
    prog = [0x20010010,   # addi at, zero, 0x10
            0x8C220000,   # lw   v0, 0(at)
            0x10000002,   # beq  zero, zero, +2
            0x20430001,   # addi v1, v0, 1   (delay slot executes)
            0x20430063,   # addi v1, v0, 99  (skipped)
            0xAC230004,   # sw   v1, 4(at)
            0x0000000D]   # break
    for k, w in enumerate(prog): put_be32(im, k * 4, w)
    put_be32(dm, 0x10, 41)
    rc.bus.sp_status = SP_STATUS_INTR_BREAK
    rc.rsp_pc = 0x04001000; rc._run_rsp_lle()
    assert be32(dm, 0x14) == 42 and rc.bus.sp_status & SP_STATUS_HALT and "SP" in rc.events
    # Vector unit: VADD signed clamp, VMUDH, VMRG on VCC, VRCP, LQV/SQV round-trip.
    rs_.vr[1] = [0x7000, 0x8000, 5, 0xFFFF, 0, 1, 2, 3]
    rs_.vr[2] = [0x2000, 0x8000, 7, 1, 0, 1, 2, 3]
    _RSP_VOPS[0x10](rs_, 3, 1, 2, 0)                           # VADD
    assert rs_.vr[3][:4] == [0x7FFF, 0x8000, 12, 0]
    _RSP_VOPS[0x07](rs_, 4, 1, 2, 0)                           # VMUDH: s16*s16 clamped
    assert rs_.vr[4][2] == 35 and rs_.vr[4][0] == 0x7FFF
    _RSP_VOPS[0x20](rs_, 5, 1, 2, 0)                           # VLT sets VCC
    rs_.vcc = 0b00000101
    _RSP_VOPS[0x27](rs_, 6, 1, 2, 0)                           # VMRG
    assert rs_.vr[6][0] == 0x7000 and rs_.vr[6][1] == 0x8000 and rs_.vr[6][2] == 5 and rs_.vr[6][3] == 1
    rs_.vr[7] = [2] * 8
    _RSP_VOPS[0x30](rs_, 8, 0, 7, 8)                           # VRCP of 2
    assert (rs_.div_out >> 16) == 0x2000 and rs_.vr[8][0] == 0  # 1/2 in the RSP's normalized format
    dm[0x200:0x210] = bytes(range(16))
    rs_.r[1] = 0x200
    rs_.lwc2((0x32 << 26) | (1 << 21) | (9 << 16) | (4 << 11))  # lqv v9[0], 0(at)
    assert rs_.vr[9][0] == 0x0001 and rs_.vr[9][7] == 0x0E0F
    rs_.r[1] = 0x300
    rs_.swc2((0x3A << 26) | (1 << 21) | (9 << 16) | (4 << 11))  # sqv v9[0], 0(at)
    assert bytes(dm[0x300:0x310]) == bytes(range(16))
    # LUV / LPV: bytes go to lane upper bits from the 8-byte-aligned block (offset masked, not address).
    dm[0x408:0x410] = bytes((0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x70, 0x80))
    rs_.r[1] = 0x408
    rs_.lwc2((0x32 << 26) | (1 << 21) | (10 << 16) | (7 << 11))  # luv v10[0], 0(at)
    assert rs_.vr[10][:4] == [0x10 << 7, 0x20 << 7, 0x30 << 7, 0x40 << 7]
    rs_.lwc2((0x32 << 26) | (1 << 21) | (11 << 16) | (6 << 11))  # lpv v11[0], 0(at)
    assert rs_.vr[11][7] == 0x8000
    # ROM database: corrected save types and Expansion Pak flags (US-030).
    def cart(code):
        r = bytearray(0x40); r[0x3C:0x3E] = code.encode(); return r
    assert detect_save_type(cart("ZS")) == SAVE_FLASHRAM and game_info(cart("ZS"))["ram8"]
    assert detect_save_type(cart("YS")) == SAVE_EEPROM_16K and detect_save_type(cart("PD")) == SAVE_EEPROM_16K
    assert detect_save_type(cart("SM")) == SAVE_EEPROM_4K and detect_save_type(cart("ZL")) == SAVE_SRAM
    assert detect_save_type(cart("QQ")) == SAVE_EEPROM_4K  # unknown → heuristic default
    # ROM browser status comes from the report file (US-043).
    with tempfile.TemporaryDirectory() as td:
        rp = os.path.join(td, "report.json")
        with open(rp, "w") as fh:
            fh.write('{"635A2BFF-8B022326": {"rating": "In-game", "first_lit_frame": 176}}')
        assert compat_report_lookup("635A2BFF-8B022326", rp)["rating"] == "In-game"
        assert compat_report_lookup("00000000-00000000", rp) == {}
    # Byte orders (.z64 / .v64 / .n64) and .zip archives all normalize to the same image (US-040).
    import zipfile
    z64 = bytes(boot_rom)
    v64 = bytearray(z64)
    for k in range(0, len(v64), 2): v64[k], v64[k + 1] = v64[k + 1], v64[k]
    n64 = bytearray(z64)
    for k in range(0, len(n64), 4): n64[k:k + 4] = n64[k:k + 4][::-1]
    assert normalize_rom_bytes(v64) == normalize_rom_bytes(z64) == normalize_rom_bytes(n64)
    with tempfile.TemporaryDirectory() as td:
        zp = os.path.join(td, "game.zip")
        with zipfile.ZipFile(zp, "w") as zf:
            zf.writestr("readme.txt", "hi")
            zf.writestr("Game (U).v64", bytes(v64))
        assert normalize_rom_bytes(read_rom_file(zp)) == normalize_rom_bytes(z64)
        lz = ACsN64Core(); lz.save_dir = None
        assert lz.load_rom(zp) is None and lz.rom_header.title.startswith("BOOTTEST")
    # Tier coverage: game-code and name matching (US-039).
    cov = compat_tier_coverage({"K": {"game_code": "NSME", "rating": "In-game", "name": "SUPER MARIO 64"}},
                               {"tier1": [{"name": "Super Mario 64", "code": "NSME"}, {"name": "Mario Kart 64", "code": "NKTE"}]})
    assert cov == ["tier1: 1/2 have a local ROM — In-game 1; missing: 1"], cov
    # Render-to-texture: pixels the RDP drew into RDRAM load back as a texture (US-037).
    rt = ACsN64Core(); rr = rt.rdp
    rr.set_color_image(0, G_IM_SIZ_16b, 8, 0x300000); rr.scissor = (0, 0, 8, 8)
    rr.omh = G_CYC_FILL << 20; rr.fill_color = 0x07C107C1          # fill green
    rr.fill_rect(0, 0, 7 << 2, 7 << 2)
    rr.set_texture_image(G_IM_FMT_RGBA, G_IM_SIZ_16b, 8, 0x300000)   # the framebuffer is now a texture
    rr.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (2 << 9), 7 << 24)
    rr.load_tile(0, (7 << 24) | (28 << 12) | 28)
    rr.set_tile((G_IM_FMT_RGBA << 21) | (G_IM_SIZ_16b << 19) | (2 << 9), 0)
    rr.set_tile_size(0, (28 << 12) | 28)
    assert rr._sampler(0, False)(3.0, 3.0) == (0, 255, 0, 255)
    # CPU reads see RDP output immediately (no separate host framebuffer).
    assert rt.bus.read_u16(0x80300000 + (3 * 8 + 3) * 2) == 0x07C1
    # hard_reset in accurate mode restarts the scheduler and clears stale events.
    hr = ACsN64Core(); hr.lle = True; hr.rom = bytearray(boot_rom); hr.rom_header = N64Header(boot_rom)
    hr.boot_lle(); hr._hle_ipl3_boot(); hr.running = True
    hr.schedule("PI", 10_000_000); hr.cpu.cp0[CP0_COUNT] = 12345; hr.frame_count = 77
    hr.hard_reset()
    assert "PI" not in hr.events and hr.now == 0 and hr.frame_count == 0 and hr.cpu.pc == 0x80000400
    # Compat harness: classification, input scripts, manual merge, regressions.
    assert compat_classify(False, 0) == "Fails"
    assert compat_classify(True, 1) == "Fails"          # static black/blank or single image
    assert compat_classify(True, 5) == "Boots"
    assert compat_classify(True, 5, error="boom") == "Fails"
    assert compat_classify(True, 5, hang="hang@80000000") == "Fails"
    sp, _ = compat_parse_script("10 - 3 0 80\n11 A 1\n", with_stick=True)
    assert sp[10] == (0, 0, 80) and sp[11] == (PAD_BUTTONS["A"], 0, 80) and 13 not in sp
    pads, meta = compat_parse_script("# rating: In-game\n300 START\n400 A,B 2\n")
    assert meta["rating"] == "In-game"
    assert pads[300] == PAD_BUTTONS["START"] and pads[304] == PAD_BUTTONS["START"] and 305 not in pads
    assert pads[401] == PAD_BUTTONS["A"] | PAD_BUTTONS["B"] and 402 not in pads
    rep = {"K": {"name": "G", "rating": "Boots"}}
    compat_merge_manual(rep, {"K": {"rating": "Playable"}})
    assert rep["K"]["rating"] == "Playable"
    assert compat_regressions({"K": {"rating": "Title"}}, {"K": {"rating": "Boots", "name": "G"}})
    assert not compat_regressions({"K": {"rating": "Boots"}}, {"K": {"rating": "Title"}})
    assert "| G |" in compat_report_md({"K": {"name": "G", "rating": "Boots"}})
    print(f"{APP_NAME}: opcode self-test passed ({len(names)} named ops, "
          f"{len(ULTRAHLE_PATCH_TABLE)} HLE patches, "
          f"{steps} steps/frame @ {1.0/max(dt,1e-6):.0f} target-Hz capable, dispatch complete)")
    return 0


def bench_main(argv: List[str]) -> int:
    """Headless speed benchmark in accurate mode: VI/s, ms/VI percentiles, per-subsystem split, output hashes."""
    import argparse, json, hashlib
    ap = argparse.ArgumentParser(prog="cathle --bench", description="Headless speed benchmark (accurate mode)")
    ap.add_argument("--bench", dest="rom", required=True, help="ROM file")
    ap.add_argument("--frames", type=int, default=300, help="VIs to time")
    ap.add_argument("--skip", type=int, default=300, help="VIs to run untimed first (boot)")
    ap.add_argument("--script", default="", help="input script (compat format), frames = absolute VI numbers")
    ap.add_argument("--state", default="", help="start from this save state instead of booting")
    ap.add_argument("--save-state", default="", help="write a save state after the skip VIs")
    ap.add_argument("--warmup", type=int, default=0, help="untimed, unhashed VIs after loading (JIT warm-up)")
    ap.add_argument("--hash", action="store_true", help="print framebuffer/RDRAM/audio hashes of the timed run")
    ap.add_argument("--json", default="", help="also write the results to this JSON file")
    ap.add_argument("--no-accel", action="store_true", help="disable numpy acceleration (pure Python)")
    ap.add_argument("--no-jit", action="store_true", help="interpret the CPU instead of the block JIT")
    ap.add_argument("--frameskip", choices=FRAMESKIP_CHOICES, default="off",
                    help="skip RDP rasterization of displayed frames (off/auto/1/2)")
    a = ap.parse_args(argv)
    if a.no_accel:
        globals()["USE_NUMPY"] = False
    random.seed(0)
    core = ACsN64Core()
    core.save_dir = None
    core.use_jit = not a.no_jit
    err = core.load_rom(a.rom, lle=True)
    if err:
        print(f"load: {err}")
        return 1
    pads: Dict[int, Any] = {}
    if a.script:
        with open(a.script) as f:
            pads, _meta = compat_parse_script(f.read(), with_stick=True)
    core.running = True
    if a.state:
        with open(a.state, "rb") as f:
            err = core.load_state(f.read())
        if err:
            print(f"state: {err}")
            return 1
    else:
        for _ in range(a.skip):
            core.set_pad(0, *pads.get(core.frame_count, (0, 0, 0)))
            core.step_frame()
    if a.save_state:
        with open(a.save_state, "wb") as f:
            f.write(core.save_state())
    core.frameskip = a.frameskip
    for _ in range(a.warmup):
        core.set_pad(0, *pads.get(core.frame_count, (0, 0, 0)))
        core.step_frame()
    # Wrap the subsystems so their time can be split out of the frame total.
    split = {"gfx": 0.0, "audio": 0.0, "vi": 0.0}
    counts = {"gfx": 0, "audio": 0, "vi": 0}
    pc = time.perf_counter
    def timed(key, fn):
        def wrapper(*args, **kw):
            t = pc()
            try:
                return fn(*args, **kw)
            finally:
                split[key] += pc() - t
                counts[key] += 1
        return wrapper
    core.process_rdp = timed("gfx", core.process_rdp)
    core.process_audio_task = timed("audio", core.process_audio_task)
    core.render_vi = timed("vi", core.render_vi)
    core.audio_out = []
    fb_hash = hashlib.sha1(); audio_hash = hashlib.sha1()
    times: List[float] = []
    t_all = pc()
    for i in range(a.frames):
        core.set_pad(0, *pads.get(core.frame_count, (0, 0, 0)))
        t = pc()
        core.step_frame()
        times.append(pc() - t)
        if a.hash:
            if core.fb_ppm:
                fb_hash.update(core.fb_ppm)
            for chunk in core.audio_out:
                audio_hash.update(chunk)
        core.audio_out.clear()
    total = pc() - t_all
    st = sorted(times)
    frame_s = sum(times)
    res: Dict[str, Any] = {
        "rom": os.path.basename(a.rom), "frames": a.frames, "start_vi": core.frame_count - a.frames,
        "accel": bool(USE_NUMPY), "jit": core.use_jit,
        "vi_per_s": round(a.frames / total, 2) if total else 0.0,
        "ms_p50": round(st[len(st) // 2] * 1000, 2) if st else 0.0,
        "ms_p95": round(st[min(len(st) - 1, int(len(st) * 0.95))] * 1000, 2) if st else 0.0,
        "frameskip": core.frameskip, "frames_skipped": core.frames_skipped,
        "gfx_tasks": counts["gfx"], "audio_tasks": counts["audio"],
        "ms_gfx_per_task": round(split["gfx"] * 1000 / counts["gfx"], 2) if counts["gfx"] else 0.0,
        "ms_audio_per_task": round(split["audio"] * 1000 / counts["audio"], 2) if counts["audio"] else 0.0,
        "split_pct": {k: round(v * 100 / frame_s, 1) for k, v in
                      (("cpu", frame_s - split["gfx"] - split["audio"] - split["vi"]),
                       ("gfx", split["gfx"]), ("audio", split["audio"]), ("vi", split["vi"]))} if frame_s else {},
    }
    if a.hash:
        res["hash_fb"] = fb_hash.hexdigest()
        res["hash_rdram"] = hashlib.sha1(core.rdram).hexdigest()
        res["hash_audio"] = audio_hash.hexdigest()
    sp = res["split_pct"]
    print(f"{res['rom']}: {res['vi_per_s']} VI/s  ms/VI p50 {res['ms_p50']} p95 {res['ms_p95']}  "
          f"gfx {res['gfx_tasks']}×{res['ms_gfx_per_task']}ms  audio {res['audio_tasks']}×{res['ms_audio_per_task']}ms  "
          f"split cpu {sp.get('cpu')}% gfx {sp.get('gfx')}% audio {sp.get('audio')}% vi {sp.get('vi')}%"
          + (f"  frameskip {core.frameskip}: {core.frames_skipped} skipped" if core.frameskip != "off" else ""))
    if a.hash:
        print(f"hash fb {res['hash_fb']} rdram {res['hash_rdram']} audio {res['hash_audio']}")
    if a.json:
        with open(a.json, "w") as f:
            json.dump(res, f, indent=2)
    return 0


def main(argv=None):
    argv = list(sys.argv[1:] if argv is None else argv)
    if "--bench" in argv:
        return bench_main(argv)
    if "--boot-test" in argv:
        return compat_main(argv)
    if "--self-test" in argv or "--opcodes" in argv:
        if "--opcodes" in argv:
            assert_opcode_table()
            print("\n".join(list_implemented_opcodes()))
            return 0
        return self_test()
    if not tk:
        print("Tkinter not available — running headless self-test")
        return self_test()
    app = CathleApp()
    app.run()
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
