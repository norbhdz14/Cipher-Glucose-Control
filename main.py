"""
Cipher Glucose Control  ·  Cipher
=================================
App móvil de control de glucosa (diabetes) en Python + Kivy, un solo archivo.
Temas Claro/Oscuro, reloj 12h/24h, iconos FontAwesome con detección automática
de glifos disponibles, recordatorios con borrado, tiras con semáforo (amarillo/rojo).
"""

import calendar
import csv
import functools
import json
import os
import math
import re
import shutil
import struct
import traceback
import uuid
import webbrowser
from datetime import date, datetime, timedelta
from urllib.parse import quote

# ======================================================================
# 1. LÓGICA PURA Y CONFIGURACIÓN DE FUENTES (FontAwesome)
# ======================================================================

from kivy.core.text import LabelBase

DIR_BASE = os.path.dirname(os.path.abspath(__file__))

_ruta_fa = os.path.join(DIR_BASE, "fonts", "fontawesome-regular-1_ufonts.com.ttf")
FA_OK = os.path.exists(_ruta_fa)
if FA_OK:
    try:
        LabelBase.register(name="FontAwesome", fn_regular=_ruta_fa)
    except Exception:
        FA_OK = False


def _leer_glifos_ttf(ruta):
    """Lee la tabla cmap del .ttf y devuelve el conjunto de códigos disponibles.
    Si algo falla devuelve un conjunto vacío (se asume que todo existe)."""
    cps = set()
    try:
        with open(ruta, "rb") as f:
            d = f.read()
        n = struct.unpack(">H", d[4:6])[0]
        tabla = None
        for i in range(n):
            tag, _cs, off, _ln = struct.unpack(">4sLLL", d[12 + 16 * i:28 + 16 * i])
            if tag == b"cmap":
                tabla = off
                break
        if tabla is None:
            return cps
        nsub = struct.unpack(">H", d[tabla + 2:tabla + 4])[0]
        for i in range(nsub):
            _pid, _eid, so = struct.unpack(">HHL", d[tabla + 4 + 8 * i:tabla + 12 + 8 * i])
            base = tabla + so
            fmt = struct.unpack(">H", d[base:base + 2])[0]
            if fmt == 4:
                segx2 = struct.unpack(">H", d[base + 6:base + 8])[0]
                seg = segx2 // 2
                fin = struct.unpack(">%dH" % seg, d[base + 14:base + 14 + segx2])
                ini = struct.unpack(">%dH" % seg, d[base + 16 + segx2:base + 16 + 2 * segx2])
                for a, b in zip(ini, fin):
                    if a != 0xFFFF and b - a < 70000:
                        cps.update(range(a, b + 1))
            elif fmt == 12:
                ng = struct.unpack(">L", d[base + 12:base + 16])[0]
                for g in range(ng):
                    a, b, _s = struct.unpack(">LLL", d[base + 16 + 12 * g:base + 28 + 12 * g])
                    if b - a < 70000:
                        cps.update(range(a, b + 1))
    except Exception:
        return set()
    return cps


GLIFOS_FA = _leer_glifos_ttf(_ruta_fa) if FA_OK else set()

# Cada icono lleva varios códigos candidatos (de más nuevo a más viejo);
# se usa el primero que exista realmente en la fuente instalada.
ICONOS = {
    "sol": ("\uf185",), "luna": ("\uf186",), "globo": ("\uf0ac",),
    "reloj": ("\uf017",), "lupa": ("\uf002",), "ayuda": ("\uf059",),
    "barcode": ("\uf02a",), "llave": ("\uf0ad",), "mas": ("\uf067",),
    "usuario": ("\uf007",), "editar": ("\uf044", "\uf040"),
    "check": ("\uf00c",), "calendario": ("\uf073",), "campana": ("\uf0f3",),
    "promedio": ("\uf1ec", "\uf080", "\uf201"),
    "tendencia": ("\uf201", "\uf080"),
    "csv": ("\uf1c3", "\uf0ce", "\uf15c", "\uf15b"),
    "txt": ("\uf15c", "\uf15b"),
    "nota": ("\uf249", "\uf040", "\uf075"),
    "pin": ("\uf3c5", "\uf041"),
    "cerrar": ("\uf00d",), "basura": ("\uf1f8", "\uf014", "\uf00d"),
    "telegram": ("\uf1d8", "\uf0e0"), "correo": ("\uf003", "\uf0e0"),
    "codigo": ("\uf121",), "aviso": ("\uf071",), "corazon": ("\uf004",),
    "paypal": ("\uf1ed", "\uf09d"),
    "peso": ("\uf24e", "\uf0e4"),
    "whatsapp": ("\uf232", "\uf1e0", "\uf064"), "respaldo": ("\uf0c7", "\uf019"),
    "importar": ("\uf093", "\uf07c", "\uf07b"),
    "info": ("\uf05a",), "medico": ("\uf0f0", "\uf0f1"), "circulo": ("\uf111",),
    "candado": ("\uf023",), "chev_d": ("\uf078",), "chev_r": ("\uf054",),
    "gota": ("\uf043",), "lista": ("\uf03a",), "grafica": ("\uf080", "\uf201"),
}


def ico(nombre, espacio=True):
    """Markup del icono (primer glifo disponible) o '' si ninguno existe."""
    if not FA_OK:
        return ""
    for c in ICONOS.get(nombre, ()):
        if not GLIFOS_FA or ord(c) in GLIFOS_FA:
            return "[font=FontAwesome]%s[/font]%s" % (c, " " if espacio else "")
    return ""


RANGO_MIN = 70            # mg/dL, límite inferior del rango normal
RANGO_MAX = 140           # mg/dL, límite superior del rango normal
STOCK_BAJO = 10           # tiras; <= este valor: ROJO
STOCK_AVISO = 15          # tiras; <= este valor: AMARILLO
TIRAS_INICIALES = 50
TIRAS_MAX = 99999
VALOR_MIN_VALIDO = 20     # mg/dL, límites de validación de entrada
VALOR_MAX_VALIDO = 600
DIAS_FILTRO = [None, 7, 14, 30, 60, 90]
MODOS_GRAFICA = ("gluc", "imc")
ZOOMS = (1.25, 1.5, 1.75, 2.0, 2.25, 2.5)   # niveles de zoom (baja visión)
ANCHO_TABLETA_DP = 720                      # desde este ancho: modo de dos columnas
LIMITE_RESPALDO = 20 * 1024 * 1024          # tamaño máximo de un archivo importado
ESTATURA_MIN, ESTATURA_MAX = 50, 250     # cm
PESO_MIN, PESO_MAX = 10, 500             # kg
CAT_IMC_ES = {"severe": "delgadez severa", "low": "bajo peso", "normal": "normal",
              "over": "sobrepeso", "obese": "obesidad", "na": "sin referencia"}

MOMENTOS_ES = ["En ayunas", "Antes de comer", "Postprandial",
               "Antes de dormir", "Madrugada", "Otro"]
MOMENTOS_EN = ["Fasting", "Before meal", "Postprandial",
               "Before bed", "Dawn", "Other"]

# Normaliza el momento (guardado en español o inglés) a un índice común
MOMENTO_IDX = {m: i for i, m in enumerate(MOMENTOS_ES)}
MOMENTO_IDX.update({m: i for i, m in enumerate(MOMENTOS_EN)})


def promedios_por_momento(lecturas):
    """{índice de momento: (promedio, cantidad)} agrupando por momento del día."""
    grupos = {}
    for r in lecturas:
        i = MOMENTO_IDX.get(r.get("momento"), len(MOMENTOS_ES) - 1)
        grupos.setdefault(i, []).append(r["valor"])
    return {i: (sum(v) / len(v), len(v)) for i, v in grupos.items()}


class ErrorUsuario(Exception):
    """Error de validación que se muestra tal cual al usuario (sin traza)."""


def estado_valor(valor):
    """Devuelve 'baja', 'normal' o 'alta' según el rango de referencia."""
    if valor < RANGO_MIN:
        return "baja"
    if valor > RANGO_MAX:
        return "alta"
    return "normal"


def categoria_imc(imc):
    # Clasificación OMS para adultos: <18.5 bajo, <25 normal, <30 sobrepeso, >=30 obesidad
    if imc < 18.5:
        return "low"
    if imc < 25:
        return "normal"
    if imc < 30:
        return "over"
    return "obese"


def _ts_num(ts):
    try:
        return datetime.fromisoformat(str(ts)).timestamp()
    except ValueError:
        return 0.0


# ----------------------------------------------------------------------
# Referencia OMS 2007 para 5-19 años: IMC para la edad (cortes en desviaciones
# estándar, DE). Fuente: OMS, "Growth reference data for 5-19 years",
# tablas simplificadas de campo (z-scores).
# Columnas: mes, -3DE, -2DE, -1DE, mediana, +1DE, +2DE, +3DE
# Interpretación OMS: delgadez < -2DE, delgadez severa < -3DE,
# sobrepeso > +1DE, obesidad > +2DE.
# ----------------------------------------------------------------------
_OMS_NINOS = """
61 12.1 13.0 14.1 15.3 16.6 18.3 20.2
62 12.1 13.0 14.1 15.3 16.6 18.3 20.2
63 12.1 13.0 14.1 15.3 16.7 18.3 20.2
64 12.1 13.0 14.1 15.3 16.7 18.3 20.3
65 12.1 13.0 14.1 15.3 16.7 18.3 20.3
66 12.1 13.0 14.1 15.3 16.7 18.4 20.4
67 12.1 13.0 14.1 15.3 16.7 18.4 20.4
68 12.1 13.0 14.1 15.3 16.7 18.4 20.5
69 12.1 13.0 14.1 15.3 16.7 18.4 20.5
70 12.1 13.0 14.1 15.3 16.7 18.5 20.6
71 12.1 13.0 14.1 15.3 16.7 18.5 20.6
72 12.1 13.0 14.1 15.3 16.8 18.5 20.7
73 12.1 13.0 14.1 15.3 16.8 18.6 20.8
74 12.2 13.1 14.1 15.3 16.8 18.6 20.8
75 12.2 13.1 14.1 15.3 16.8 18.6 20.9
76 12.2 13.1 14.1 15.4 16.8 18.7 21.0
77 12.2 13.1 14.1 15.4 16.9 18.7 21.0
78 12.2 13.1 14.1 15.4 16.9 18.7 21.1
79 12.2 13.1 14.1 15.4 16.9 18.8 21.2
80 12.2 13.1 14.2 15.4 16.9 18.8 21.3
81 12.2 13.1 14.2 15.4 17.0 18.9 21.3
82 12.2 13.1 14.2 15.4 17.0 18.9 21.4
83 12.2 13.1 14.2 15.5 17.0 19.0 21.5
84 12.3 13.1 14.2 15.5 17.0 19.0 21.6
85 12.3 13.2 14.2 15.5 17.1 19.1 21.7
86 12.3 13.2 14.2 15.5 17.1 19.1 21.8
87 12.3 13.2 14.3 15.5 17.1 19.2 21.9
88 12.3 13.2 14.3 15.6 17.2 19.2 22.0
89 12.3 13.2 14.3 15.6 17.2 19.3 22.0
90 12.3 13.2 14.3 15.6 17.2 19.3 22.1
91 12.3 13.2 14.3 15.6 17.3 19.4 22.2
92 12.3 13.2 14.3 15.6 17.3 19.4 22.4
93 12.4 13.3 14.3 15.7 17.3 19.5 22.5
94 12.4 13.3 14.4 15.7 17.4 19.6 22.6
95 12.4 13.3 14.4 15.7 17.4 19.6 22.7
96 12.4 13.3 14.4 15.7 17.4 19.7 22.8
97 12.4 13.3 14.4 15.8 17.5 19.7 22.9
98 12.4 13.3 14.4 15.8 17.5 19.8 23.0
99 12.4 13.3 14.4 15.8 17.5 19.9 23.1
100 12.4 13.4 14.5 15.8 17.6 19.9 23.3
101 12.5 13.4 14.5 15.9 17.6 20.0 23.4
102 12.5 13.4 14.5 15.9 17.7 20.1 23.5
103 12.5 13.4 14.5 15.9 17.7 20.1 23.6
104 12.5 13.4 14.5 15.9 17.7 20.2 23.8
105 12.5 13.4 14.6 16.0 17.8 20.3 23.9
106 12.5 13.5 14.6 16.0 17.8 20.3 24.0
107 12.5 13.5 14.6 16.0 17.9 20.4 24.2
108 12.6 13.5 14.6 16.0 17.9 20.5 24.3
109 12.6 13.5 14.6 16.1 18.0 20.5 24.4
110 12.6 13.5 14.7 16.1 18.0 20.6 24.6
111 12.6 13.5 14.7 16.1 18.0 20.7 24.7
112 12.6 13.6 14.7 16.2 18.1 20.8 24.9
113 12.6 13.6 14.7 16.2 18.1 20.8 25.0
114 12.7 13.6 14.8 16.2 18.2 20.9 25.1
115 12.7 13.6 14.8 16.3 18.2 21.0 25.3
116 12.7 13.6 14.8 16.3 18.3 21.1 25.5
117 12.7 13.7 14.8 16.3 18.3 21.2 25.6
118 12.7 13.7 14.9 16.4 18.4 21.2 25.8
119 12.8 13.7 14.9 16.4 18.4 21.3 25.9
120 12.8 13.7 14.9 16.4 18.5 21.4 26.1
121 12.8 13.8 15.0 16.5 18.5 21.5 26.2
122 12.8 13.8 15.0 16.5 18.6 21.6 26.4
123 12.8 13.8 15.0 16.6 18.6 21.7 26.6
124 12.9 13.8 15.0 16.6 18.7 21.7 26.7
125 12.9 13.9 15.1 16.6 18.8 21.8 26.9
126 12.9 13.9 15.1 16.7 18.8 21.9 27.0
127 12.9 13.9 15.1 16.7 18.9 22.0 27.2
128 13.0 13.9 15.2 16.8 18.9 22.1 27.4
129 13.0 14.0 15.2 16.8 19.0 22.2 27.5
130 13.0 14.0 15.2 16.9 19.0 22.3 27.7
131 13.0 14.0 15.3 16.9 19.1 22.4 27.9
132 13.1 14.1 15.3 16.9 19.2 22.5 28.0
133 13.1 14.1 15.3 17.0 19.2 22.5 28.2
134 13.1 14.1 15.4 17.0 19.3 22.6 28.4
135 13.1 14.1 15.4 17.1 19.3 22.7 28.5
136 13.2 14.2 15.5 17.1 19.4 22.8 28.7
137 13.2 14.2 15.5 17.2 19.5 22.9 28.8
138 13.2 14.2 15.5 17.2 19.5 23.0 29.0
139 13.2 14.3 15.6 17.3 19.6 23.1 29.2
140 13.3 14.3 15.6 17.3 19.7 23.2 29.3
141 13.3 14.3 15.7 17.4 19.7 23.3 29.5
142 13.3 14.4 15.7 17.4 19.8 23.4 29.6
143 13.4 14.4 15.7 17.5 19.9 23.5 29.8
144 13.4 14.5 15.8 17.5 19.9 23.6 30.0
145 13.4 14.5 15.8 17.6 20.0 23.7 30.1
146 13.5 14.5 15.9 17.6 20.1 23.8 30.3
147 13.5 14.6 15.9 17.7 20.2 23.9 30.4
148 13.5 14.6 16.0 17.8 20.2 24.0 30.6
149 13.6 14.6 16.0 17.8 20.3 24.1 30.7
150 13.6 14.7 16.1 17.9 20.4 24.2 30.9
151 13.6 14.7 16.1 17.9 20.4 24.3 31.0
152 13.7 14.8 16.2 18.0 20.5 24.4 31.1
153 13.7 14.8 16.2 18.0 20.6 24.5 31.3
154 13.7 14.8 16.3 18.1 20.7 24.6 31.4
155 13.8 14.9 16.3 18.2 20.8 24.7 31.6
156 13.8 14.9 16.4 18.2 20.8 24.8 31.7
157 13.8 15.0 16.4 18.3 20.9 24.9 31.8
158 13.9 15.0 16.5 18.4 21.0 25.0 31.9
159 13.9 15.1 16.5 18.4 21.1 25.1 32.1
160 14.0 15.1 16.6 18.5 21.1 25.2 32.2
161 14.0 15.2 16.6 18.6 21.2 25.2 32.3
162 14.0 15.2 16.7 18.6 21.3 25.3 32.4
163 14.1 15.2 16.7 18.7 21.4 25.4 32.6
164 14.1 15.3 16.8 18.7 21.5 25.5 32.7
165 14.1 15.3 16.8 18.8 21.5 25.6 32.8
166 14.2 15.4 16.9 18.9 21.6 25.7 32.9
167 14.2 15.4 17.0 18.9 21.7 25.8 33.0
168 14.3 15.5 17.0 19.0 21.8 25.9 33.1
169 14.3 15.5 17.1 19.1 21.8 26.0 33.2
170 14.3 15.6 17.1 19.1 21.9 26.1 33.3
171 14.4 15.6 17.2 19.2 22.0 26.2 33.4
172 14.4 15.7 17.2 19.3 22.1 26.3 33.5
173 14.5 15.7 17.3 19.3 22.2 26.4 33.5
174 14.5 15.7 17.3 19.4 22.2 26.5 33.6
175 14.5 15.8 17.4 19.5 22.3 26.5 33.7
176 14.6 15.8 17.4 19.5 22.4 26.6 33.8
177 14.6 15.9 17.5 19.6 22.5 26.7 33.9
178 14.6 15.9 17.5 19.6 22.5 26.8 33.9
179 14.7 16.0 17.6 19.7 22.6 26.9 34.0
180 14.7 16.0 17.6 19.8 22.7 27.0 34.1
181 14.7 16.1 17.7 19.8 22.8 27.1 34.1
182 14.8 16.1 17.8 19.9 22.8 27.1 34.2
183 14.8 16.1 17.8 20.0 22.9 27.2 34.3
184 14.8 16.2 17.9 20.0 23.0 27.3 34.3
185 14.9 16.2 17.9 20.1 23.0 27.4 34.4
186 14.9 16.3 18.0 20.1 23.1 27.4 34.5
187 15.0 16.3 18.0 20.2 23.2 27.5 34.5
188 15.0 16.3 18.1 20.3 23.3 27.6 34.6
189 15.0 16.4 18.1 20.3 23.3 27.7 34.6
190 15.0 16.4 18.2 20.4 23.4 27.7 34.7
191 15.1 16.5 18.2 20.4 23.5 27.8 34.7
192 15.1 16.5 18.2 20.5 23.5 27.9 34.8
193 15.1 16.5 18.3 20.6 23.6 27.9 34.8
194 15.2 16.6 18.3 20.6 23.7 28.0 34.8
195 15.2 16.6 18.4 20.7 23.7 28.1 34.9
196 15.2 16.7 18.4 20.7 23.8 28.1 34.9
197 15.3 16.7 18.5 20.8 23.8 28.2 35.0
198 15.3 16.7 18.5 20.8 23.9 28.3 35.0
199 15.3 16.8 18.6 20.9 24.0 28.3 35.0
200 15.3 16.8 18.6 20.9 24.0 28.4 35.1
201 15.4 16.8 18.7 21.0 24.1 28.5 35.1
202 15.4 16.9 18.7 21.0 24.2 28.5 35.1
203 15.4 16.9 18.7 21.1 24.2 28.6 35.2
204 15.4 16.9 18.8 21.1 24.3 28.6 35.2
205 15.5 17.0 18.8 21.2 24.3 28.7 35.2
206 15.5 17.0 18.9 21.2 24.4 28.7 35.2
207 15.5 17.0 18.9 21.3 24.4 28.8 35.3
208 15.5 17.1 18.9 21.3 24.5 28.9 35.3
209 15.6 17.1 19.0 21.4 24.5 28.9 35.3
210 15.6 17.1 19.0 21.4 24.6 29.0 35.3
211 15.6 17.1 19.1 21.5 24.7 29.0 35.4
212 15.6 17.2 19.1 21.5 24.7 29.1 35.4
213 15.6 17.2 19.1 21.6 24.8 29.1 35.4
214 15.7 17.2 19.2 21.6 24.8 29.2 35.4
215 15.7 17.3 19.2 21.7 24.9 29.2 35.4
216 15.7 17.3 19.2 21.7 24.9 29.2 35.4
217 15.7 17.3 19.3 21.8 25.0 29.3 35.4
218 15.7 17.3 19.3 21.8 25.0 29.3 35.5
219 15.7 17.4 19.3 21.8 25.1 29.4 35.5
220 15.8 17.4 19.4 21.9 25.1 29.4 35.5
221 15.8 17.4 19.4 21.9 25.1 29.5 35.5
222 15.8 17.4 19.4 22.0 25.2 29.5 35.5
223 15.8 17.5 19.5 22.0 25.2 29.5 35.5
224 15.8 17.5 19.5 22.0 25.3 29.6 35.5
225 15.8 17.5 19.5 22.1 25.3 29.6 35.5
226 15.8 17.5 19.6 22.1 25.4 29.6 35.5
227 15.8 17.5 19.6 22.2 25.4 29.7 35.5
228 15.9 17.6 19.6 22.2 25.4 29.7 35.5
"""

_OMS_NINAS = """
61 11.8 12.7 13.9 15.2 16.9 18.9 21.3
62 11.8 12.7 13.9 15.2 16.9 18.9 21.4
63 11.8 12.7 13.9 15.2 16.9 18.9 21.5
64 11.8 12.7 13.9 15.2 16.9 18.9 21.5
65 11.7 12.7 13.9 15.2 16.9 19.0 21.6
66 11.7 12.7 13.9 15.2 16.9 19.0 21.7
67 11.7 12.7 13.9 15.2 16.9 19.0 21.7
68 11.7 12.7 13.9 15.3 17.0 19.1 21.8
69 11.7 12.7 13.9 15.3 17.0 19.1 21.9
70 11.7 12.7 13.9 15.3 17.0 19.1 22.0
71 11.7 12.7 13.9 15.3 17.0 19.2 22.1
72 11.7 12.7 13.9 15.3 17.0 19.2 22.1
73 11.7 12.7 13.9 15.3 17.0 19.3 22.2
74 11.7 12.7 13.9 15.3 17.0 19.3 22.3
75 11.7 12.7 13.9 15.3 17.1 19.3 22.4
76 11.7 12.7 13.9 15.3 17.1 19.4 22.5
77 11.7 12.7 13.9 15.3 17.1 19.4 22.6
78 11.7 12.7 13.9 15.3 17.1 19.5 22.7
79 11.7 12.7 13.9 15.3 17.2 19.5 22.8
80 11.7 12.7 13.9 15.3 17.2 19.6 22.9
81 11.7 12.7 13.9 15.4 17.2 19.6 23.0
82 11.7 12.7 13.9 15.4 17.2 19.7 23.1
83 11.7 12.7 13.9 15.4 17.3 19.7 23.2
84 11.8 12.7 13.9 15.4 17.3 19.8 23.3
85 11.8 12.7 13.9 15.4 17.3 19.8 23.4
86 11.8 12.8 14.0 15.4 17.4 19.9 23.5
87 11.8 12.8 14.0 15.5 17.4 20.0 23.6
88 11.8 12.8 14.0 15.5 17.4 20.0 23.7
89 11.8 12.8 14.0 15.5 17.5 20.1 23.9
90 11.8 12.8 14.0 15.5 17.5 20.1 24.0
91 11.8 12.8 14.0 15.5 17.5 20.2 24.1
92 11.8 12.8 14.0 15.6 17.6 20.3 24.2
93 11.8 12.8 14.1 15.6 17.6 20.3 24.4
94 11.9 12.9 14.1 15.6 17.6 20.4 24.5
95 11.9 12.9 14.1 15.7 17.7 20.5 24.6
96 11.9 12.9 14.1 15.7 17.7 20.6 24.8
97 11.9 12.9 14.1 15.7 17.8 20.6 24.9
98 11.9 12.9 14.2 15.7 17.8 20.7 25.1
99 11.9 12.9 14.2 15.8 17.9 20.8 25.2
100 11.9 13.0 14.2 15.8 17.9 20.9 25.3
101 12.0 13.0 14.2 15.8 18.0 20.9 25.5
102 12.0 13.0 14.3 15.9 18.0 21.0 25.6
103 12.0 13.0 14.3 15.9 18.1 21.1 25.8
104 12.0 13.0 14.3 15.9 18.1 21.2 25.9
105 12.0 13.1 14.3 16.0 18.2 21.3 26.1
106 12.1 13.1 14.4 16.0 18.2 21.3 26.2
107 12.1 13.1 14.4 16.1 18.3 21.4 26.4
108 12.1 13.1 14.4 16.1 18.3 21.5 26.5
109 12.1 13.2 14.5 16.1 18.4 21.6 26.7
110 12.1 13.2 14.5 16.2 18.4 21.7 26.8
111 12.2 13.2 14.5 16.2 18.5 21.8 27.0
112 12.2 13.2 14.6 16.3 18.6 21.9 27.2
113 12.2 13.3 14.6 16.3 18.6 21.9 27.3
114 12.2 13.3 14.6 16.3 18.7 22.0 27.5
115 12.3 13.3 14.7 16.4 18.7 22.1 27.6
116 12.3 13.4 14.7 16.4 18.8 22.2 27.8
117 12.3 13.4 14.7 16.5 18.8 22.3 27.9
118 12.3 13.4 14.8 16.5 18.9 22.4 28.1
119 12.4 13.4 14.8 16.6 19.0 22.5 28.2
120 12.4 13.5 14.8 16.6 19.0 22.6 28.4
121 12.4 13.5 14.9 16.7 19.1 22.7 28.5
122 12.4 13.5 14.9 16.7 19.2 22.8 28.7
123 12.5 13.6 15.0 16.8 19.2 22.8 28.8
124 12.5 13.6 15.0 16.8 19.3 22.9 29.0
125 12.5 13.6 15.0 16.9 19.4 23.0 29.1
126 12.5 13.7 15.1 16.9 19.4 23.1 29.3
127 12.6 13.7 15.1 17.0 19.5 23.2 29.4
128 12.6 13.7 15.2 17.0 19.6 23.3 29.6
129 12.6 13.8 15.2 17.1 19.6 23.4 29.7
130 12.7 13.8 15.3 17.1 19.7 23.5 29.9
131 12.7 13.8 15.3 17.2 19.8 23.6 30.0
132 12.7 13.9 15.3 17.2 19.9 23.7 30.2
133 12.8 13.9 15.4 17.3 19.9 23.8 30.3
134 12.8 14.0 15.4 17.4 20.0 23.9 30.5
135 12.8 14.0 15.5 17.4 20.1 24.0 30.6
136 12.9 14.0 15.5 17.5 20.2 24.1 30.8
137 12.9 14.1 15.6 17.5 20.2 24.2 30.9
138 12.9 14.1 15.6 17.6 20.3 24.3 31.1
139 13.0 14.2 15.7 17.7 20.4 24.4 31.2
140 13.0 14.2 15.7 17.7 20.5 24.5 31.4
141 13.0 14.3 15.8 17.8 20.6 24.7 31.5
142 13.1 14.3 15.8 17.9 20.6 24.8 31.6
143 13.1 14.3 15.9 17.9 20.7 24.9 31.8
144 13.2 14.4 16.0 18.0 20.8 25.0 31.9
145 13.2 14.4 16.0 18.1 20.9 25.1 32.0
146 13.2 14.5 16.1 18.1 21.0 25.2 32.2
147 13.3 14.5 16.1 18.2 21.1 25.3 32.3
148 13.3 14.6 16.2 18.3 21.1 25.4 32.4
149 13.3 14.6 16.2 18.3 21.2 25.5 32.6
150 13.4 14.7 16.3 18.4 21.3 25.6 32.7
151 13.4 14.7 16.3 18.5 21.4 25.7 32.8
152 13.5 14.8 16.4 18.5 21.5 25.8 33.0
153 13.5 14.8 16.4 18.6 21.6 25.9 33.1
154 13.5 14.8 16.5 18.7 21.6 26.0 33.2
155 13.6 14.9 16.6 18.7 21.7 26.1 33.3
156 13.6 14.9 16.6 18.8 21.8 26.2 33.4
157 13.6 15.0 16.7 18.9 21.9 26.3 33.6
158 13.7 15.0 16.7 18.9 22.0 26.4 33.7
159 13.7 15.1 16.8 19.0 22.0 26.5 33.8
160 13.8 15.1 16.8 19.1 22.1 26.6 33.9
161 13.8 15.2 16.9 19.1 22.2 26.7 34.0
162 13.8 15.2 16.9 19.2 22.3 26.8 34.1
163 13.9 15.2 17.0 19.3 22.4 26.9 34.2
164 13.9 15.3 17.0 19.3 22.4 27.0 34.3
165 13.9 15.3 17.1 19.4 22.5 27.1 34.4
166 14.0 15.4 17.1 19.4 22.6 27.1 34.5
167 14.0 15.4 17.2 19.5 22.7 27.2 34.6
168 14.0 15.4 17.2 19.6 22.7 27.3 34.7
169 14.1 15.5 17.3 19.6 22.8 27.4 34.7
170 14.1 15.5 17.3 19.7 22.9 27.5 34.8
171 14.1 15.6 17.4 19.7 22.9 27.6 34.9
172 14.1 15.6 17.4 19.8 23.0 27.7 35.0
173 14.2 15.6 17.5 19.9 23.1 27.7 35.1
174 14.2 15.7 17.5 19.9 23.1 27.8 35.1
175 14.2 15.7 17.6 20.0 23.2 27.9 35.2
176 14.3 15.7 17.6 20.0 23.3 28.0 35.3
177 14.3 15.8 17.6 20.1 23.3 28.0 35.4
178 14.3 15.8 17.7 20.1 23.4 28.1 35.4
179 14.3 15.8 17.7 20.2 23.5 28.2 35.5
180 14.4 15.9 17.8 20.2 23.5 28.2 35.5
181 14.4 15.9 17.8 20.3 23.6 28.3 35.6
182 14.4 15.9 17.8 20.3 23.6 28.4 35.7
183 14.4 16.0 17.9 20.4 23.7 28.4 35.7
184 14.5 16.0 17.9 20.4 23.7 28.5 35.8
185 14.5 16.0 17.9 20.4 23.8 28.5 35.8
186 14.5 16.0 18.0 20.5 23.8 28.6 35.8
187 14.5 16.1 18.0 20.5 23.9 28.6 35.9
188 14.5 16.1 18.0 20.6 23.9 28.7 35.9
189 14.5 16.1 18.1 20.6 24.0 28.7 36.0
190 14.6 16.1 18.1 20.6 24.0 28.8 36.0
191 14.6 16.2 18.1 20.7 24.1 28.8 36.0
192 14.6 16.2 18.2 20.7 24.1 28.9 36.1
193 14.6 16.2 18.2 20.7 24.1 28.9 36.1
194 14.6 16.2 18.2 20.8 24.2 29.0 36.1
195 14.6 16.2 18.2 20.8 24.2 29.0 36.1
196 14.6 16.2 18.3 20.8 24.3 29.0 36.2
197 14.6 16.3 18.3 20.9 24.3 29.1 36.2
198 14.7 16.3 18.3 20.9 24.3 29.1 36.2
199 14.7 16.3 18.3 20.9 24.4 29.1 36.2
200 14.7 16.3 18.3 20.9 24.4 29.2 36.2
201 14.7 16.3 18.4 21.0 24.4 29.2 36.3
202 14.7 16.3 18.4 21.0 24.4 29.2 36.3
203 14.7 16.3 18.4 21.0 24.5 29.3 36.3
204 14.7 16.4 18.4 21.0 24.5 29.3 36.3
205 14.7 16.4 18.4 21.1 24.5 29.3 36.3
206 14.7 16.4 18.4 21.1 24.6 29.3 36.3
207 14.7 16.4 18.5 21.1 24.6 29.4 36.3
208 14.7 16.4 18.5 21.1 24.6 29.4 36.3
209 14.7 16.4 18.5 21.1 24.6 29.4 36.3
210 14.7 16.4 18.5 21.2 24.6 29.4 36.3
211 14.7 16.4 18.5 21.2 24.7 29.4 36.3
212 14.7 16.4 18.5 21.2 24.7 29.5 36.3
213 14.7 16.4 18.5 21.2 24.7 29.5 36.3
214 14.7 16.4 18.5 21.2 24.7 29.5 36.3
215 14.7 16.4 18.6 21.2 24.8 29.5 36.3
216 14.7 16.4 18.6 21.3 24.8 29.5 36.3
217 14.7 16.5 18.6 21.3 24.8 29.5 36.3
218 14.7 16.5 18.6 21.3 24.8 29.6 36.3
219 14.7 16.5 18.6 21.3 24.8 29.6 36.3
220 14.7 16.5 18.6 21.3 24.8 29.6 36.3
221 14.7 16.5 18.6 21.3 24.9 29.6 36.2
222 14.7 16.5 18.6 21.3 24.9 29.6 36.2
223 14.7 16.5 18.6 21.4 24.9 29.6 36.2
224 14.7 16.5 18.6 21.4 24.9 29.6 36.2
225 14.7 16.5 18.7 21.4 24.9 29.6 36.2
226 14.7 16.5 18.7 21.4 24.9 29.6 36.2
227 14.7 16.5 18.7 21.4 25.0 29.7 36.2
228 14.7 16.5 18.7 21.4 25.0 29.7 36.2
"""


def _parse_tabla_oms(txt):
    tabla = {}
    for linea in txt.strip().splitlines():
        p = linea.split()
        if len(p) == 8:
            tabla[int(p[0])] = tuple(float(x) for x in p[1:])
    return tabla


OMS_IMC = {"M": _parse_tabla_oms(_OMS_NINOS), "F": _parse_tabla_oms(_OMS_NINAS)}
EDAD_MIN_MESES = 61        # la referencia OMS empieza a los 5 años y 1 mes
EDAD_ADULTO_MESES = 228    # 19 años: desde aquí se usan los cortes de adultos


def cortes_oms(sexo, meses):
    """Cortes (-3DE, -2DE, -1DE, mediana, +1DE, +2DE, +3DE) para una edad en
    meses (admite fracciones, se interpola). None si no hay referencia."""
    tabla = OMS_IMC.get(sexo)
    if not tabla or meses is None or meses < EDAD_MIN_MESES or meses >= EDAD_ADULTO_MESES:
        return None
    m0 = int(meses)
    m1 = min(m0 + 1, EDAD_ADULTO_MESES)
    f = meses - m0
    a, b = tabla[m0], tabla[m1]
    return tuple(a[i] + (b[i] - a[i]) * f for i in range(7))


def clasificar_imc(imc, meses, sexo):
    """'severe' | 'low' | 'normal' | 'over' | 'obese' | 'na'.
    Adultos (19+ o edad desconocida): cortes 18.5 / 25 / 30.
    5-18 años: IMC para la edad OMS 2007. Menores de 5 años: 'na' (sin tabla)."""
    if meses is None or meses >= EDAD_ADULTO_MESES:
        return categoria_imc(imc)
    cortes = cortes_oms(sexo, meses)
    if cortes is None:
        return "na"
    if imc < cortes[0]:
        return "severe"
    if imc < cortes[1]:
        return "low"
    if imc > cortes[5]:
        return "obese"
    if imc > cortes[4]:
        return "over"
    return "normal"


def _restar_meses(fecha, meses):
    n = fecha.year * 12 + (fecha.month - 1) - meses
    y, m0 = divmod(n, 12)
    m = m0 + 1
    return date(y, m, min(fecha.day, calendar.monthrange(y, m)[1]))


class Perfil:
    """Un usuario: lecturas cronológicas + inventario + recordatorios."""

    def __init__(self, nombre, id_=None, lecturas=None, tiras=TIRAS_INICIALES, recordatorios=None,
                 sexo=None, estatura=None, medidas=None, nacimiento=None):
        self.id = id_ or uuid.uuid4().hex[:8]
        self.nombre = nombre
        self.lecturas = list(lecturas or [])
        self.sexo = sexo if sexo in ("M", "F") else None
        self.estatura = estatura          # cm
        self.medidas = list(medidas or [])  # [{"ts", "peso"}]
        self.nacimiento = nacimiento        # fecha ISO aproximada (se calcula con la edad indicada)
        try:
            self.tiras = max(0, int(tiras))
        except (TypeError, ValueError):
            self.tiras = TIRAS_INICIALES
        if recordatorios is None:
            recordatorios = [
                {"titulo": "Desayuno / Breakfast", "hora": "08:00 AM", "activo": True},
                {"titulo": "Comida / Lunch", "hora": "02:30 PM", "activo": True},
                {"titulo": "Cena / Dinner", "hora": "08:00 PM", "activo": True},
            ]
        self.recordatorios = [r for r in recordatorios
                              if isinstance(r, dict) and "titulo" in r]
        for r in self.recordatorios:
            r.setdefault("hora", "08:00 AM")
            r.setdefault("activo", True)

    def registrar(self, valor, momento="Otro", notas="", ts=None):
        try:
            valor = float(valor)
        except (TypeError, ValueError):
            raise ErrorUsuario("Introduce un valor numérico de glucosa. / Enter a numeric glucose value.")
        if not (VALOR_MIN_VALIDO <= valor <= VALOR_MAX_VALIDO):
            raise ErrorUsuario(
                "El valor debe estar entre %d y %d mg/dL."
                % (VALOR_MIN_VALIDO, VALOR_MAX_VALIDO)
            )
        if valor == int(valor):
            valor = int(valor)

        lectura = {
            "ts": ts or datetime.now().isoformat(timespec="seconds"),
            "valor": valor,
            "momento": momento,
            "notas": (notas or "").strip(),
        }
        self.lecturas.append(lectura)
        self.lecturas.sort(key=lambda r: r["ts"])
        self.tiras = max(0, self.tiras - 1)
        return lectura

    def establecer_tiras(self, cantidad):
        cantidad = int(cantidad)
        if cantidad < 0:
            raise ErrorUsuario("El inventario no puede ser negativo. / Inventory cannot be negative.")
        if cantidad > TIRAS_MAX:
            raise ErrorUsuario("Cantidad demasiado grande. / Amount too large.")
        self.tiras = cantidad

    def anadir_tiras(self, cantidad):
        cantidad = int(cantidad)
        if cantidad <= 0:
            raise ErrorUsuario("Escribe una cantidad mayor que 0. / Enter an amount greater than 0.")
        self.establecer_tiras(self.tiras + cantidad)

    @property
    def stock_bajo(self):
        return self.tiras <= STOCK_BAJO

    @property
    def nivel_tiras(self):
        """'rojo' (<=10), 'amarillo' (<=15) o 'ok'."""
        if self.tiras <= STOCK_BAJO:
            return "rojo"
        if self.tiras <= STOCK_AVISO:
            return "amarillo"
        return "ok"

    def lecturas_filtradas(self, dias=None):
        if dias is None:
            return list(self.lecturas)
        limite = datetime.now() - timedelta(days=dias)
        res = []
        for r in self.lecturas:
            try:
                if datetime.fromisoformat(r["ts"]) >= limite:
                    res.append(r)
            except ValueError:
                continue
        return res

    def promedio_filtrado(self, dias=None):
        vals = [r["valor"] for r in self.lecturas_filtradas(dias)]
        if not vals:
            return None
        return sum(vals) / len(vals)

    # ---------------- datos corporales / IMC ----------------
    def registrar_cuerpo(self, sexo, estatura, peso, edad_anios=None, edad_meses=None, ts=None):
        if sexo not in ("M", "F"):
            raise ErrorUsuario("Selecciona el sexo. / Select sex.")
        try:
            solo_datos = not str(peso or "").strip() and bool(self.medidas)
            est = float(str(estatura).replace(",", "."))
            pes = None if solo_datos else float(str(peso).replace(",", "."))
        except (TypeError, ValueError):
            raise ErrorUsuario("Estatura y peso deben ser números. / Height and weight must be numbers.")
        if not (ESTATURA_MIN <= est <= ESTATURA_MAX):
            raise ErrorUsuario("La estatura debe estar entre %d y %d cm." % (ESTATURA_MIN, ESTATURA_MAX))
        if pes is not None and not (PESO_MIN <= pes <= PESO_MAX):
            raise ErrorUsuario("El peso debe estar entre %d y %d kg." % (PESO_MIN, PESO_MAX))
        nac = self.nacimiento
        a_txt = "" if edad_anios is None else str(edad_anios).strip()
        if a_txt:
            try:
                anios = int(a_txt)
                meses = int(str(edad_meses).strip() or 0) if edad_meses is not None else 0
            except ValueError:
                raise ErrorUsuario("La edad debe ser un número entero. / Age must be a whole number.")
            if not (0 <= anios <= 120) or not (0 <= meses <= 11):
                raise ErrorUsuario("Edad no válida (años 0-120, meses 0-11). / Invalid age.")
            nac = _restar_meses(date.today(), anios * 12 + meses).isoformat()
        elif not nac:
            raise ErrorUsuario("Indica la edad. / Enter the age.")
        self.nacimiento = nac
        self.sexo = sexo
        self.estatura = est
        if pes is not None:
            self.medidas.append({"ts": ts or datetime.now().isoformat(timespec="seconds"),
                                 "peso": round(pes, 1)})
            self.medidas.sort(key=lambda m: m["ts"])

    def registrar_peso(self, peso, ts=None):
        if not self.estatura or self.sexo not in ("M", "F"):
            raise ErrorUsuario("Primero registra sexo y estatura. / Enter sex and height first.")
        try:
            pes = float(str(peso).replace(",", "."))
        except (TypeError, ValueError):
            raise ErrorUsuario("El peso debe ser un número. / Weight must be a number.")
        if not (PESO_MIN <= pes <= PESO_MAX):
            raise ErrorUsuario("El peso debe estar entre %d y %d kg." % (PESO_MIN, PESO_MAX))
        self.medidas.append({"ts": ts or datetime.now().isoformat(timespec="seconds"),
                             "peso": round(pes, 1)})
        self.medidas.sort(key=lambda m: m["ts"])

    @property
    def tiene_datos_cuerpo(self):
        return bool(self.sexo and self.estatura and self.medidas and self.nacimiento)

    def imc_de(self, peso):
        if not self.estatura:
            return None
        return peso / ((self.estatura / 100.0) ** 2)

    def edad_meses(self, ts=None):
        if not self.nacimiento:
            return None
        try:
            nac = date.fromisoformat(self.nacimiento)
            ref = datetime.fromisoformat(str(ts)).date() if ts else date.today()
        except ValueError:
            return None
        return (ref.year - nac.year) * 12 + ref.month - nac.month - (1 if ref.day < nac.day else 0)

    def edad_partes(self):
        m = self.edad_meses()
        return None if m is None or m < 0 else (m // 12, m % 12)

    def categoria_en(self, imc, ts=None):
        m = self.edad_meses(ts)
        if m is not None and m < 0:
            return "na"
        return clasificar_imc(imc, m, self.sexo)

    def refs_para(self, tiempos):
        # curvas OMS (t, -2DE, +1DE, +2DE) para menores de 5 a 18 años; [] si no aplica
        if not self.nacimiento:
            return []
        try:
            nac = datetime.combine(date.fromisoformat(self.nacimiento), datetime.min.time()).timestamp()
        except ValueError:
            return []
        marcas = sorted({_ts_num(x) for x in tiempos})
        if len(marcas) == 1:
            marcas = [marcas[0] - 15 * 86400, marcas[0], marcas[0] + 15 * 86400]
        res = []
        for tn in marcas:
            c = cortes_oms(self.sexo, (tn - nac) / (30.4375 * 86400.0))
            if c:
                res.append((tn, c[1], c[4], c[5]))
        return res if len(res) >= 2 else []

    @property
    def peso_actual(self):
        return self.medidas[-1]["peso"] if self.medidas else None

    @property
    def imc_actual(self):
        return self.imc_de(self.peso_actual) if self.medidas else None

    def medidas_con_imc(self, dias=None):
        limite = datetime.now() - timedelta(days=dias) if dias is not None else None
        res = []
        for m in self.medidas:
            try:
                if limite is not None and datetime.fromisoformat(m["ts"]) < limite:
                    continue
            except ValueError:
                continue
            res.append((m["ts"], m["peso"], self.imc_de(m["peso"])))
        return res

    def fusionar(self, otro):
        """Agrega lo que falte de `otro` sin borrar ni duplicar nada.
        Devuelve (lecturas, pesos, recordatorios) nuevos."""
        vistas = {(r["ts"], r["valor"], r.get("momento")) for r in self.lecturas}
        n_l = 0
        for r in otro.lecturas:
            k = (r["ts"], r["valor"], r.get("momento"))
            if k not in vistas:
                vistas.add(k)
                self.lecturas.append(dict(r))
                n_l += 1
        self.lecturas.sort(key=lambda r: r["ts"])
        pesos = {(m["ts"], m["peso"]) for m in self.medidas}
        n_m = 0
        for m in otro.medidas:
            k = (m["ts"], m["peso"])
            if k not in pesos:
                pesos.add(k)
                self.medidas.append(dict(m))
                n_m += 1
        self.medidas.sort(key=lambda m: m["ts"])
        recs = {(r["titulo"], r["hora"]) for r in self.recordatorios}
        n_r = 0
        for r in otro.recordatorios:
            k = (r["titulo"], r["hora"])
            if k not in recs:
                recs.add(k)
                self.recordatorios.append(dict(r))
                n_r += 1
        if not self.sexo and otro.sexo:
            self.sexo = otro.sexo
        if not self.estatura and otro.estatura:
            self.estatura = otro.estatura
        if not self.nacimiento and otro.nacimiento:
            self.nacimiento = otro.nacimiento
        return n_l, n_m, n_r

    def ultimas(self, n=30):
        return self.lecturas[-n:]

    def to_dict(self):
        return {
            "id": self.id,
            "nombre": self.nombre,
            "tiras": self.tiras,
            "lecturas": self.lecturas,
            "recordatorios": self.recordatorios,
            "sexo": self.sexo,
            "estatura": self.estatura,
            "medidas": self.medidas,
            "nacimiento": self.nacimiento,
        }

    @classmethod
    def from_dict(cls, d):
        lecturas = []
        for r in d.get("lecturas", []):
            try:
                datetime.fromisoformat(str(r["ts"]))
                v = float(r["valor"])
                lecturas.append({
                    "ts": str(r["ts"]),
                    "valor": int(v) if v.is_integer() else v,
                    "momento": r.get("momento", "Otro"),
                    "notas": r.get("notas", ""),
                })
            except (KeyError, TypeError, ValueError, AttributeError):
                continue
        lecturas.sort(key=lambda r: r["ts"])
        medidas = []
        for m in d.get("medidas", []):
            try:
                datetime.fromisoformat(str(m["ts"]))
                medidas.append({"ts": str(m["ts"]), "peso": float(m["peso"])})
            except (KeyError, TypeError, ValueError, AttributeError):
                continue
        medidas.sort(key=lambda m: m["ts"])
        try:
            estatura = float(d.get("estatura")) if d.get("estatura") else None
        except (TypeError, ValueError):
            estatura = None
        try:
            nac = d.get("nacimiento")
            if nac:
                date.fromisoformat(str(nac))
            nac = str(nac) if nac else None
        except ValueError:
            nac = None
        return cls(
            nombre=d.get("nombre", "Usuario"),
            id_=d.get("id"),
            lecturas=lecturas,
            tiras=d.get("tiras", TIRAS_INICIALES),
            recordatorios=d.get("recordatorios", None),
            sexo=d.get("sexo"),
            estatura=estatura,
            medidas=medidas,
            nacimiento=nac,
        )


class _Etiqueta:
    # objeto mínimo con `nombre`, para reutilizar el generador de nombres de archivo
    def __init__(self, nombre):
        self.nombre = nombre


class GestorGlucosa:
    def __init__(self, ruta):
        self.ruta = ruta
        self.perfiles = {}
        self.activo_id = None

    @property
    def activo(self):
        return self.perfiles[self.activo_id]

    def nombres(self):
        return [p.nombre for p in self.perfiles.values()]

    def crear_perfil(self, nombre):
        nombre = (nombre or "").strip()
        if not nombre:
            raise ErrorUsuario("Escribe un nombre para el perfil. / Enter a profile name.")
        if nombre.lower() in (n.lower() for n in self.nombres()):
            raise ErrorUsuario("Ya existe un perfil con ese nombre. / Profile already exists.")
        perfil = Perfil(nombre)
        self.perfiles[perfil.id] = perfil
        self.activo_id = perfil.id
        self.guardar()
        return perfil

    def cambiar_por_nombre(self, nombre):
        for p in self.perfiles.values():
            if p.nombre == nombre:
                self.activo_id = p.id
                self.guardar()
                return p
        raise ErrorUsuario("Perfil no encontrado. / Profile not found.")

    def cargar(self):
        if os.path.exists(self.ruta):
            try:
                with open(self.ruta, "r", encoding="utf-8") as f:
                    datos = json.load(f)
                for d in datos.get("perfiles", []):
                    p = Perfil.from_dict(d)
                    self.perfiles[p.id] = p
                self.activo_id = datos.get("activo")
            except (OSError, ValueError, AttributeError, TypeError):
                try:
                    os.replace(self.ruta, self.ruta + ".corrupto")
                except OSError:
                    pass
                self.perfiles = {}
        if not self.perfiles:
            p = Perfil("Principal")
            self.perfiles[p.id] = p
        if self.activo_id not in self.perfiles:
            self.activo_id = next(iter(self.perfiles))
        self.guardar()

    def guardar(self):
        carpeta = os.path.dirname(self.ruta)
        if carpeta:
            os.makedirs(carpeta, exist_ok=True)
        datos = {
            "version": 1,
            "activo": self.activo_id,
            "perfiles": [p.to_dict() for p in self.perfiles.values()],
        }
        tmp = self.ruta + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(datos, f, ensure_ascii=False, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, self.ruta)

    # ---------------- respaldo completo e importación ----------------
    def exportar_respaldo(self, carpeta_respaldo):
        def escribir(ruta):
            datos = {
                "app": "CipherGlucose", "version": 1,
                "exportado": datetime.now().isoformat(timespec="seconds"),
                "activo": self.activo_id,
                "perfiles": [p.to_dict() for p in self.perfiles.values()],
            }
            with open(ruta, "w", encoding="utf-8") as f:
                json.dump(datos, f, ensure_ascii=False, indent=2)
        return self._escribir_export(_Etiqueta("respaldo"), "json", escribir, carpeta_respaldo)

    @staticmethod
    def _sanear_perfil(p):
        # nunca se confía en el contenido del archivo: se valida cada campo
        p.nombre = str(p.nombre).strip()[:40] or "Usuario"
        p.id = str(p.id)[:16] or uuid.uuid4().hex[:8]
        lect = []
        for r in p.lecturas:
            try:
                v = float(r["valor"])
            except (KeyError, TypeError, ValueError):
                continue
            if not (VALOR_MIN_VALIDO <= v <= VALOR_MAX_VALIDO):
                continue
            lect.append({"ts": str(r["ts"]), "valor": int(v) if v == int(v) else v,
                         "momento": str(r.get("momento", "Otro"))[:30] or "Otro",
                         "notas": str(r.get("notas", ""))[:300]})
        lect.sort(key=lambda r: r["ts"])
        p.lecturas = lect
        p.medidas = [m for m in p.medidas if PESO_MIN <= m["peso"] <= PESO_MAX]
        if p.estatura is not None and not (ESTATURA_MIN <= p.estatura <= ESTATURA_MAX):
            p.estatura = None
        p.tiras = max(0, min(int(p.tiras), TIRAS_MAX))
        recs = []
        for r in p.recordatorios:
            recs.append({"titulo": str(r.get("titulo", ""))[:60],
                         "hora": str(r.get("hora", "08:00 AM"))[:10],
                         "activo": bool(r.get("activo", True))})
        p.recordatorios = [r for r in recs if r["titulo"]]
        return p

    @staticmethod
    def leer_respaldo(ruta):
        """Lee un archivo .json (respaldo completo) o .csv (exportación de un perfil).
        Devuelve (tipo, datos, activo_id); lanza ErrorUsuario si no es válido."""
        if not ruta or not os.path.isfile(ruta):
            raise ErrorUsuario("No se encontró el archivo. / File not found.")
        try:
            if os.path.getsize(ruta) > LIMITE_RESPALDO:
                raise ErrorUsuario("El archivo es demasiado grande. / File too large.")
        except OSError:
            raise ErrorUsuario("No se puede leer el archivo. / Cannot read the file.")
        ext = os.path.splitext(ruta)[1].lower()

        if ext == ".json":
            try:
                with open(ruta, "r", encoding="utf-8-sig") as f:
                    datos = json.load(f)
            except (OSError, ValueError, UnicodeDecodeError):
                raise ErrorUsuario("El archivo no es un respaldo válido. / Not a valid backup.")
            lista = datos.get("perfiles") if isinstance(datos, dict) else None
            if not isinstance(lista, list):
                raise ErrorUsuario("El archivo no es un respaldo de Cipher. / Not a Cipher backup.")
            perfiles = []
            for d in lista[:50]:
                if not isinstance(d, dict):
                    continue
                try:
                    perfiles.append(GestorGlucosa._sanear_perfil(Perfil.from_dict(d)))
                except Exception:
                    continue
            if not perfiles:
                raise ErrorUsuario("El respaldo no contiene perfiles válidos. / No valid profiles.")
            return "json", perfiles, str(datos.get("activo"))[:16]

        if ext == ".csv":
            perfil = Perfil("CSV", recordatorios=[])
            seccion = None
            try:
                with open(ruta, "r", encoding="utf-8-sig", newline="") as f:
                    for fila in csv.reader(f):
                        if not fila or not any(c.strip() for c in fila):
                            continue
                        cab = [c.strip().lower() for c in fila]
                        if cab[0] == "fecha_hora":
                            seccion = "peso" if len(cab) > 1 and cab[1] == "peso_kg" else "glucosa"
                            continue
                        try:
                            ts = datetime.fromisoformat(fila[0].strip()).isoformat(timespec="seconds")
                            if seccion == "glucosa":
                                v = float(fila[1])
                                if not (VALOR_MIN_VALIDO <= v <= VALOR_MAX_VALIDO):
                                    continue
                                perfil.lecturas.append({
                                    "ts": ts, "valor": int(v) if v == int(v) else v,
                                    "momento": (fila[2].strip() if len(fila) > 2 else "")[:30] or "Otro",
                                    "notas": (fila[4].strip() if len(fila) > 4 else "")[:300]})
                            elif seccion == "peso":
                                pes = float(fila[1])
                                if not (PESO_MIN <= pes <= PESO_MAX):
                                    continue
                                perfil.medidas.append({"ts": ts, "peso": round(pes, 1)})
                                if len(fila) > 4 and fila[4].strip() in ("M", "F") and not perfil.sexo:
                                    perfil.sexo = fila[4].strip()
                                if len(fila) > 5 and fila[5].strip() and not perfil.estatura:
                                    est = float(fila[5])
                                    if ESTATURA_MIN <= est <= ESTATURA_MAX:
                                        perfil.estatura = est
                                if len(fila) > 6 and fila[6].strip().isdigit() and not perfil.nacimiento \
                                        and int(fila[6]) <= 1440:
                                    perfil.nacimiento = _restar_meses(
                                        datetime.fromisoformat(ts).date(), int(fila[6])).isoformat()
                        except (ValueError, IndexError, OverflowError):
                            continue
            except (OSError, UnicodeDecodeError, csv.Error):
                raise ErrorUsuario("No se pudo leer el CSV. / Could not read the CSV.")
            if not perfil.lecturas and not perfil.medidas:
                raise ErrorUsuario("El CSV no contiene datos reconocibles. / No recognizable data.")
            perfil.lecturas.sort(key=lambda r: r["ts"])
            perfil.medidas.sort(key=lambda m: m["ts"])
            return "csv", GestorGlucosa._sanear_perfil(perfil), None

        raise ErrorUsuario("Formato no compatible: usa un archivo .json o .csv. / Unsupported format.")

    def importar(self, tipo, datos, modo, activo_id=None, destino=None):
        """modo: 'fusionar' (agrega lo que falte) o 'reemplazar' (solo JSON; guarda copia previa)."""
        res = {"perfiles": 0, "lecturas": 0, "pesos": 0, "recordatorios": 0}
        if tipo == "json" and modo == "reemplazar":
            try:
                if os.path.exists(self.ruta):
                    shutil.copy2(self.ruta, self.ruta + ".antes_de_importar")
            except OSError:
                pass
            nuevos = {p.id: p for p in datos}
            self.perfiles = nuevos
            self.activo_id = activo_id if activo_id in nuevos else next(iter(nuevos))
            res["perfiles"] = len(nuevos)
            res["lecturas"] = sum(len(p.lecturas) for p in nuevos.values())
            res["pesos"] = sum(len(p.medidas) for p in nuevos.values())
            res["recordatorios"] = sum(len(p.recordatorios) for p in nuevos.values())
        elif tipo == "csv":
            a, b, c = (destino or self.activo).fusionar(datos)
            res.update(lecturas=a, pesos=b, recordatorios=c)
        else:
            for p in datos:
                d = self.perfiles.get(p.id)
                if d is None:
                    d = next((x for x in self.perfiles.values()
                              if x.nombre.lower() == p.nombre.lower()), None)
                if d is None:
                    self.perfiles[p.id] = p
                    res["perfiles"] += 1
                    res["lecturas"] += len(p.lecturas)
                    res["pesos"] += len(p.medidas)
                    res["recordatorios"] += len(p.recordatorios)
                else:
                    a, b, c = d.fusionar(p)
                    res["lecturas"] += a
                    res["pesos"] += b
                    res["recordatorios"] += c
        self.guardar()
        return res

    @staticmethod
    def _candidatos_exportacion(carpeta_respaldo):
        return [
            "/storage/emulated/0/Download",
            "/sdcard/Download",
            carpeta_respaldo,
        ]

    def _escribir_export(self, perfil, ext, escritor, carpeta_respaldo):
        seguro = re.sub(r"[^\w\-]+", "_", perfil.nombre).strip("_") or "perfil"
        nombre = "glucosa_%s_%s.%s" % (
            seguro, datetime.now().strftime("%Y%m%d_%H%M%S"), ext)
        ultimo_error = None
        if platform == "android" and carpeta_respaldo and os.path.isdir(carpeta_respaldo):
            # Android 10+: se escribe en la carpeta privada y se copia a Descargas con MediaStore
            tmp = os.path.join(carpeta_respaldo, nombre)
            try:
                escritor(tmp)
                destino = guardar_en_descargas(tmp, nombre, MIME_EXPORT.get(ext, "application/octet-stream"))
                if destino:
                    try:
                        os.remove(tmp)
                    except OSError:
                        pass
                    return destino
                return tmp
            except OSError as exc:
                ultimo_error = exc
        for carpeta in self._candidatos_exportacion(carpeta_respaldo):
            if not carpeta or not os.path.isdir(carpeta):
                continue
            ruta = os.path.join(carpeta, nombre)
            try:
                escritor(ruta)
                return ruta
            except OSError as exc:
                ultimo_error = exc
        raise ErrorUsuario("No se pudo exportar: %s" % (ultimo_error or "sin carpeta"))

    def exportar_csv(self, perfil, carpeta_respaldo):
        def escribir(ruta):
            with open(ruta, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f)
                w.writerow(["fecha_hora", "glucosa_mg_dl", "momento", "estado", "notas"])
                for r in perfil.lecturas:
                    w.writerow([r["ts"], r["valor"], r["momento"],
                                estado_valor(r["valor"]), r["notas"]])
                if perfil.medidas:
                    w.writerow([])
                    w.writerow(["fecha_hora", "peso_kg", "imc", "categoria_imc", "sexo", "estatura_cm", "edad_meses"])
                    for ts, pes, imc in perfil.medidas_con_imc():
                        w.writerow([ts, pes, ("%.1f" % imc) if imc else "",
                                    CAT_IMC_ES[perfil.categoria_en(imc, ts)] if imc else "",
                                    perfil.sexo or "", perfil.estatura or "",
                                    perfil.edad_meses(ts) if perfil.nacimiento else ""])
        return self._escribir_export(perfil, "csv", escribir, carpeta_respaldo)

    def exportar_txt(self, perfil, carpeta_respaldo):
        def escribir(ruta):
            prom = perfil.promedio_filtrado()
            with open(ruta, "w", encoding="utf-8") as f:
                f.write("CIPHER GLUCOSE CONTROL\n")
                f.write("Perfil: %s\n" % perfil.nombre)
                f.write("Generado: %s\n" % datetime.now().strftime("%d/%m/%Y %H:%M"))
                f.write("Lecturas: %d  |  Promedio: %s  |  Tiras: %d\n" % (
                    len(perfil.lecturas),
                    ("%.0f mg/dL" % prom) if prom is not None else "—",
                    perfil.tiras))
                f.write("Rango normal de referencia: %d-%d mg/dL\n" % (RANGO_MIN, RANGO_MAX))
                f.write("-" * 56 + "\n")
                for r in perfil.lecturas:
                    f.write("%s | %5s mg/dL | %-15s | %s\n" % (
                        r["ts"].replace("T", " "), r["valor"], r["momento"],
                        r["notas"]))
                if perfil.medidas:
                    f.write("-" * 56 + "\n")
                    f.write("PESO E IMC  |  Sexo: %s  |  Estatura: %g cm\n" % (
                        perfil.sexo or "—", perfil.estatura or 0))
                    for ts, pes, imc in perfil.medidas_con_imc():
                        f.write("%s | %6.1f kg | IMC %s | %s\n" % (
                            ts.replace("T", " "), pes,
                            ("%.1f" % imc) if imc else "—",
                            CAT_IMC_ES[perfil.categoria_en(imc, ts)] if imc else ""))
                f.write("-" * 56 + "\n")
                f.write(AVISO_EXPORT + "\n")
        return self._escribir_export(perfil, "txt", escribir, carpeta_respaldo)


# ======================================================================
# 2. UTILIDADES DE INTERFAZ Y TRADUCCIONES
# ======================================================================

from kivy.app import App
from kivy.clock import Clock
from kivy.core.text import Label as CoreLabel
from kivy.core.window import Window
from kivy.graphics import Color, Ellipse, Line, Mesh, Rectangle, RoundedRectangle
from kivy.metrics import dp, sp
from kivy.properties import ListProperty, StringProperty
from kivy.uix.boxlayout import BoxLayout
from kivy.uix.button import Button
from kivy.uix.gridlayout import GridLayout
from kivy.uix.label import Label
from kivy.uix.popup import Popup
from kivy.uix.scrollview import ScrollView
from kivy.uix.spinner import Spinner, SpinnerOption
from kivy.uix.textinput import TextInput
from kivy.uix.widget import Widget
from kivy.uix.filechooser import FileChooserListView
from kivy.uix.image import Image
from kivy.uix.behaviors import ButtonBehavior
from kivy.utils import escape_markup, platform
try:
    from kivy.core.text.markup import MarkupLabel as CoreMarkup
except Exception:
    CoreMarkup = None

TEMAS = {
    "dark": {
        "BG": (0.06, 0.08, 0.12, 1),
        "CARD": (0.12, 0.16, 0.24, 1),
        "CARD2": (0.18, 0.23, 0.33, 1),
        "TEXTO": (0.96, 0.98, 1.0, 1),
        "TEXTO_SUAVE": (0.78, 0.84, 0.92, 1),
        "ROJO_OSCURO": (0.45, 0.12, 0.15, 1),
        "AMARILLO": (1.0, 0.82, 0.20, 1),
        "AMARILLO_OSCURO": (0.40, 0.32, 0.08, 1),
    },
    "light": {
        "BG": (0.88, 0.91, 0.96, 1),
        "CARD": (1.0, 1.0, 1.0, 1),
        "CARD2": (0.82, 0.87, 0.93, 1),
        "TEXTO": (0.08, 0.12, 0.18, 1),
        "TEXTO_SUAVE": (0.30, 0.38, 0.48, 1),
        "ROJO_OSCURO": (0.95, 0.78, 0.78, 1),
        "AMARILLO": (0.78, 0.52, 0.0, 1),
        "AMARILLO_OSCURO": (0.99, 0.93, 0.70, 1),
    }
}

CIAN = (0.12, 0.75, 0.92, 1)
VIOLETA = (0.60, 0.25, 0.85, 1)
AZUL = (0.18, 0.42, 0.92, 1)
VERDE = (0.20, 0.78, 0.44, 1)
ROJO = (0.92, 0.25, 0.25, 1)
GRIS = (0.3, 0.3, 0.3, 1)
NARANJA = (0.96, 0.55, 0.10, 1)
VERDE_WA = (0.15, 0.72, 0.33, 1)
COLOR_ESTADO = {"baja": ROJO, "normal": VERDE, "alta": ROJO}


# ----------------------------------------------------------------------
# Contraste uniforme (WCAG): los colores de acento se ajustan al fondo real
# sobre el que se dibujan, tanto en tema claro como oscuro.
# ----------------------------------------------------------------------

def tema_cols():
    app = App.get_running_app()
    return TEMAS.get(getattr(app, "tema_actual", "dark"), TEMAS["dark"])


def _lin(c):
    return c / 12.92 if c <= 0.03928 else ((c + 0.055) / 1.055) ** 2.4


def luminancia(rgba):
    r, g, b = (_lin(x) for x in rgba[:3])
    return 0.2126 * r + 0.7152 * g + 0.0722 * b


def razon_contraste(a, b):
    la, lb_ = luminancia(a), luminancia(b)
    return (max(la, lb_) + 0.05) / (min(la, lb_) + 0.05)


def asegurar_contraste(col, fondo, minimo=4.5):
    """Oscurece (sobre fondo claro) o aclara (sobre fondo oscuro) el color
    hasta alcanzar la razón de contraste mínima contra el fondo."""
    c = tuple(col[:3])
    objetivo = 0.0 if luminancia(fondo) > 0.4 else 1.0
    for _ in range(30):
        if razon_contraste(c, fondo) >= minimo:
            break
        c = tuple(x + (objetivo - x) * 0.12 for x in c)
    return c + (1,)


def col_t(col, fondo=None, minimo=4.5):
    return asegurar_contraste(col, fondo if fondo is not None else tema_cols()["CARD"], minimo)


def texto_sobre(fondo):
    # texto blanco si contrasta >= 3.5 (texto grande y en negrita), si no, casi negro
    if razon_contraste((1, 1, 1), fondo) >= 3.5:
        return (1, 1, 1, 1)
    return (0.04, 0.06, 0.10, 1)


def color_cat(cat):
    if cat in ("severe", "obese"):
        return ROJO
    if cat == "normal":
        return VERDE
    if cat == "na":
        return (0.55, 0.58, 0.64, 1)
    return tema_cols()["AMARILLO"]


def escala_ui():
    return getattr(App.get_running_app(), "factor_escala_global", 1.25)


def k_alto():
    # a partir de zoom 1.5 las cajas crecen un poco para que quepa la letra mayor
    return max(1.0, 1.0 + (escala_ui() - 1.5) * 0.5)


def popup_tema(title, content, **kw):
    c = tema_cols()
    kw.setdefault("separator_color", CIAN)
    kw.setdefault("title_size", sp(15) * min(escala_ui(), 1.6))
    sh = kw.get("size_hint")
    if sh and Window.width >= dp(ANCHO_TABLETA_DP):
        kw["size_hint"] = (min(sh[0], 0.6), sh[1])     # no ocupar todo el ancho en tableta
    return Popup(
        title=title, content=content, background="", background_color=c["BG"],
        title_color=c["TEXTO"], **kw)

TEXTOS = {
    "es": {
        "app_title": "Control de Glucosa",
        "about": "Soporte",
        "new_user": "+ Usuario",
        "strips": "TIRAS",
        "avg": "PROMEDIO",
        "add_strips": "Añadir",
        "new_reading": "Nueva lectura",
        "past_reading": "Registrar lectura pasada (Papel)",
        "reminders_btn": "Recordatorios de Comidas",
        "placeholder_val": "Ej. 110",
        "placeholder_notes": "Notas u observaciones opcionales...",
        "register_btn": "Registrar lectura",
        "trend": "Tendencia",
        "filter_all": "Todo",
        "filter_1w": "1 semana",
        "filter_2w": "2 semanas",
        "filter_1m": "1 mes",
        "filter_2m": "2 meses",
        "filter_3m": "3 meses",
        "export_csv": "Exportar CSV",
        "export_txt": "Exportar TXT",
        "history": "Historial reciente",
        "no_readings": "Aún no hay lecturas registradas.",
        "readings_count": "lecturas",
        "reading_one": "lectura",
        "period_avg": "Promedio del periodo:",
        "st_baja": "baja",
        "st_normal": "normal",
        "st_alta": "alta",
        "theme_light": "Claro",
        "theme_dark": "Oscuro",
        "no_strips_alert": "¡Sin tiras!",
        "low_stock_alert": "¡Stock bajo!",
        "close": "Cerrar",
        "save": "Guardar",
        "cancel": "Cancelar",
        "create": "Crear",
        "delete": "Eliminar",
        "ok": "Aceptar",
        "new_profile_title": "Añadir nuevo perfil",
        "profile_name_hint": "Nombre del usuario",
        "strip_inv_title": "Añadir tiras",
        "strip_inv_prompt": "Tiras actuales: %d\n¿Cuántas quieres añadir?",
        "strip_add_hint": "Cantidad",
        "strip_set_total": "Fijar total",
        "export_ready": "Exportación lista",
        "file_saved": "Archivo guardado en:\n%s",
        "dev_role": "Sistemas computacionales IoT",
        "dev_section": "Desarrollador",
        "contact_support": "Contacto y soporte",
        "support_project": "Apoya el proyecto",
        "support_desc": "Si Cipher te resulta útil, tu apoyo ayuda a seguir desarrollándolo y mejorándolo.",
        "about_popup_title": "Soporte / Cipher",
        "past_popup_title": "Selecciona Fecha y Hora 12h (Papel)",
        "past_date": "Fecha (Día / Mes / Año):",
        "past_time": "Hora (1-12) y AM/PM:",
        "past_gluc": "Glucosa y Momento:",
        "save_past": "Guardar lectura pasada",
        "reminders_title": "Recordatorios Programados",
        "rem_time": "Hora del recordatorio (1-12) y AM/PM:",
        "add_reminder": "Añadir Recordatorio",
        "rem_name_hint": "Ej: Antes del Desayuno",
        "delete_rem_q": "¿Eliminar el recordatorio\n\"%s\"?",
        "report_error": "Enviar reporte de error",
        "body_title": "Peso e IMC",
        "sex": "Sexo",
        "sex_m": "Hombre",
        "sex_f": "Mujer",
        "height_cm": "Estatura (cm)",
        "weight_kg": "Peso (kg)",
        "bmi": "IMC",
        "bmi_low": "Bajo peso",
        "bmi_normal": "Normal",
        "bmi_over": "Sobrepeso",
        "bmi_obese": "Obesidad",
        "register_weight": "Registrar peso",
        "weight_hist": "Historial de peso",
        "chart_gluc": "Glucosa",
        "chart_bmi": "IMC",
        "chart_both": "Glucosa + IMC",
        "body_needed": "Toca Registrar peso para completar tus datos",
        "later": "Después",
        "body_update_prompt": "Actualiza sexo, edad o estatura. Deja el peso vacío si no quieres registrar uno nuevo.",
        "tab_gluc": "Glucosa",
        "tab_bmi": "IMC",
        "tab_stats": "Estadísticas",
        "tab_hist": "Historial",
        "bmi_severe": "Delgadez severa",
        "bmi_na": "Sin referencia",
        "bmi_ref_child": "Referencia OMS 5-19 años (edad y sexo)",
        "bmi_ref_na": "Menores de 5 años: la OMS usa otras tablas (peso para la talla) que esta app aún no incluye. Consulta al pediatra.",
        "bmi_ref_note": "DE = desviaciones estándar. Es orientación, no diagnóstico. El rango de glucosa de la app (70-140) es de adultos; en menores, las metas las define su médico.",
        "age_years": "Edad (años)",
        "age_months": "Meses (0-11)",
        "age_fmt": "%d años %d m",
        "sd_abbr": "DE",
        "help_title": "Ayuda",
        "help_intro": "Toca cada tema para abrirlo o cerrarlo.",
        "disc_title": "Aviso importante",
        "disc_text": """• Esta app es una [b]herramienta personal de registro[/b] (glucosa, peso, tiras e IMC). [b]No es un dispositivo médico.[/b]
• Fue desarrollada por el [b]Ing. Norberto Hernández, ingeniero en sistemas computacionales[/b]. [b]No es médico ni profesional de la salud.[/b]
• [b]No diagnostica, no trata ni previene enfermedades[/b], y no calcula dosis de insulina ni de medicamentos.
• Los colores, rangos y categorías son [b]referencias generales[/b]; no sustituyen las metas que defina tu médico.
• Úsala [b]siempre bajo supervisión médica[/b]. Antes de cambiar tu tratamiento, dieta o actividad física, consulta a tu médico.
• En una emergencia (confusión, desmayo, convulsiones, dificultad para respirar), llama a tu número local de emergencias (en México, 911).
• La app se ofrece "tal cual", sin garantías. Verifica tus lecturas con tu glucómetro y tu equipo médico. El desarrollador no se hace responsable por decisiones tomadas con base en la información de la app.""",
        "disc_accept": "Entiendo y acepto",
        "disc_short": "Úsala bajo supervisión médica. Fue creada por un ingeniero en sistemas, no por un médico; no diagnostica ni sustituye la atención médica.",
        "cedula": "Cédula profesional (ingeniería): 15061201",
        "rem_note_title": "Recordatorio activado",
        "rem_note": "No se pudieron usar las notificaciones del teléfono (falta la librería plyer o el permiso). A la hora indicada verás un aviso dentro de la app mientras esté abierta.",
        "dedic_title": "Dedicatoria",
        "dedic_text": "Con todo mi amor y gratitud a mi madre, [b]Aurora Guzmán[/b]; a mi esposa, [b]Lorena Contreras[/b]; y a mi abuela materna, [b]Socorro Hernández[/b].\n\nEsta app nace pensando en ellas, en todas las personas que viven con diabetes y en quienes las acompañan.",
        "by_moment": "Promedio por momento del día",
        "share_wa": "Compartir por WhatsApp",
        "wa_profile": "Perfil", "wa_period": "Periodo", "wa_avg": "Promedio", "wa_min": "Mín",
        "wa_max": "Máx", "wa_inrange": "En rango", "wa_last": "Últimas lecturas", "wa_weight": "Peso",
        "wa_disclaimer": "Aviso: registro personal; no sustituye la valoración médica. Úsalo bajo supervisión médica.",
        "wa_copied": "No se pudo abrir WhatsApp. El resumen se copió al portapapeles: pégalo en el chat.",
        "wa_fail": "No se pudo abrir WhatsApp ni copiar el resumen.",
        "rem_title": "Hora de tu control de glucosa",
        "export_backup": "Exportar respaldo (JSON)",
        "import_btn": "Importar / Cargar respaldo",
        "import_title": "Importar datos",
        "import_hint": "Elige un archivo .json (respaldo completo) o .csv (exportación de un perfil), o escribe su ruta abajo.",
        "import_path_hint": "Ruta del archivo…",
        "import_load": "Cargar",
        "import_found": "Archivo reconocido",
        "import_json_sum": "Respaldo con %d perfil(es), %d lectura(s) y %d peso(s).",
        "import_csv_sum": "CSV con %d lectura(s) y %d peso(s). Se agregará al perfil activo: %s.",
        "import_merge": "Fusionar",
        "import_replace": "Reemplazar todo",
        "import_replace_warn": "Fusionar agrega lo que falte sin borrar nada. Reemplazar sustituye TODOS tus datos actuales (antes se guarda una copia automática).",
        "import_done": "Importación lista",
        "import_done_txt": "Perfiles: %d · Lecturas: %d · Pesos: %d · Recordatorios: %d",
        "stats_title": "Resumen del periodo",
        "stat_min": "Mínimo",
        "stat_max": "Máximo",
        "stat_inrange": "En rango (70-140)",
        "stat_out": "Altas / Bajas",
        "stat_wchange": "Cambio de peso",
        "bmi_ref": "Referencia IMC (OMS, adultos)",
        "no_weights": "Aún no hay pesos registrados.",
        "hist_weight": "Peso",
        "past_weight_btn": "Peso pasado (Papel)",
        "past_weight_title": "Peso pasado: fecha y hora 12h",
        "body_prompt": "Indica sexo, edad, estatura y peso para calcular el IMC.",
    },
    "en": {
        "app_title": "Glucose Control",
        "about": "Support",
        "new_user": "+ User",
        "strips": "STRIPS",
        "avg": "AVERAGE",
        "add_strips": "Add",
        "new_reading": "New reading",
        "past_reading": "Register past reading (Paper)",
        "reminders_btn": "Meal Reminders",
        "placeholder_val": "Ex. 110",
        "placeholder_notes": "Optional notes or observations...",
        "register_btn": "Register reading",
        "trend": "Trend",
        "filter_all": "All",
        "filter_1w": "1 week",
        "filter_2w": "2 weeks",
        "filter_1m": "1 month",
        "filter_2m": "2 months",
        "filter_3m": "3 months",
        "export_csv": "Export CSV",
        "export_txt": "Export TXT",
        "history": "Recent history",
        "no_readings": "No readings recorded yet.",
        "readings_count": "readings",
        "reading_one": "reading",
        "period_avg": "Period average:",
        "st_baja": "low",
        "st_normal": "normal",
        "st_alta": "high",
        "theme_light": "Light",
        "theme_dark": "Dark",
        "no_strips_alert": "No strips!",
        "low_stock_alert": "Low stock!",
        "close": "Close",
        "save": "Save",
        "cancel": "Cancel",
        "create": "Create",
        "delete": "Delete",
        "ok": "OK",
        "new_profile_title": "Add new profile",
        "profile_name_hint": "User name",
        "strip_inv_title": "Add strips",
        "strip_inv_prompt": "Current strips: %d\nHow many do you want to add?",
        "strip_add_hint": "Amount",
        "strip_set_total": "Set total",
        "export_ready": "Export ready",
        "file_saved": "File saved at:\n%s",
        "dev_role": "IoT Computer Systems",
        "dev_section": "Developer",
        "contact_support": "Contact & Support",
        "support_project": "Support the project",
        "support_desc": "If Cipher is useful to you, your support helps continue developing and improving it.",
        "about_popup_title": "Support / Cipher",
        "past_popup_title": "Select Date & Time 12h (Paper)",
        "past_date": "Date (Day / Month / Year):",
        "past_time": "Time (1-12) and AM/PM:",
        "past_gluc": "Glucose and Moment:",
        "save_past": "Save past reading",
        "reminders_title": "Scheduled Reminders",
        "rem_time": "Reminder time (1-12) and AM/PM:",
        "add_reminder": "Add Reminder",
        "rem_name_hint": "Ex: Before Breakfast",
        "delete_rem_q": "Delete reminder\n\"%s\"?",
        "report_error": "Send error report",
        "body_title": "Weight & BMI",
        "sex": "Sex",
        "sex_m": "Male",
        "sex_f": "Female",
        "height_cm": "Height (cm)",
        "weight_kg": "Weight (kg)",
        "bmi": "BMI",
        "bmi_low": "Underweight",
        "bmi_normal": "Normal",
        "bmi_over": "Overweight",
        "bmi_obese": "Obesity",
        "register_weight": "Log weight",
        "weight_hist": "Weight history",
        "chart_gluc": "Glucose",
        "chart_bmi": "BMI",
        "chart_both": "Glucose + BMI",
        "body_needed": "Tap Log weight to complete your data",
        "later": "Later",
        "body_update_prompt": "Update sex, age or height. Leave weight empty if you do not want to log a new one.",
        "tab_gluc": "Glucose",
        "tab_bmi": "BMI",
        "tab_stats": "Stats",
        "tab_hist": "History",
        "bmi_severe": "Severe thinness",
        "bmi_na": "No reference",
        "bmi_ref_child": "WHO reference 5-19 years (age & sex)",
        "bmi_ref_na": "Under 5 years: WHO uses other tables (weight-for-height) that this app does not include yet. Ask the pediatrician.",
        "bmi_ref_note": "SD = standard deviations. Guidance only, not a diagnosis. The app's glucose range (70-140) is for adults; for minors, targets are set by their doctor.",
        "age_years": "Age (years)",
        "age_months": "Months (0-11)",
        "age_fmt": "%dy %dm",
        "sd_abbr": "SD",
        "help_title": "Help",
        "help_intro": "Tap each topic to open or close it.",
        "disc_title": "Important notice",
        "disc_text": """• This app is a [b]personal logging tool[/b] (glucose, weight, strips and BMI). [b]It is not a medical device.[/b]
• It was developed by [b]Eng. Norberto Hernández, a computer systems engineer[/b]. [b]He is not a physician or a health professional.[/b]
• [b]It does not diagnose, treat or prevent any disease[/b], and it does not calculate insulin or medication doses.
• Colors, ranges and categories are [b]general references[/b]; they do not replace the targets set by your doctor.
• Use it [b]always under medical supervision[/b]. Before changing your treatment, diet or physical activity, consult your doctor.
• In an emergency (confusion, fainting, seizures, trouble breathing), call your local emergency number.
• The app is provided "as is", without warranties. Check your readings with your meter and your medical team. The developer is not liable for decisions made based on the information in the app.""",
        "disc_accept": "I understand and accept",
        "disc_short": "Use under medical supervision. It was created by a systems engineer, not a physician; it does not diagnose or replace medical care.",
        "cedula": "Professional ID (engineering): 15061201",
        "rem_note_title": "Reminder on",
        "rem_note": "Phone notifications could not be used (plyer library or permission missing). At the set time you will see an in-app alert while the app is open.",
        "dedic_title": "Dedication",
        "dedic_text": "With all my love and gratitude to my mother, [b]Aurora Guzmán[/b]; my wife, [b]Lorena Contreras[/b]; and my maternal grandmother, [b]Socorro Hernández[/b].\n\nThis app was born thinking of them, of everyone living with diabetes, and of those who care for them.",
        "by_moment": "Average by time of day",
        "share_wa": "Share via WhatsApp",
        "wa_profile": "Profile", "wa_period": "Period", "wa_avg": "Average", "wa_min": "Min",
        "wa_max": "Max", "wa_inrange": "In range", "wa_last": "Latest readings", "wa_weight": "Weight",
        "wa_disclaimer": "Notice: personal log; it does not replace medical assessment. Use under medical supervision.",
        "wa_copied": "Could not open WhatsApp. The summary was copied to the clipboard: paste it in the chat.",
        "wa_fail": "Could not open WhatsApp or copy the summary.",
        "rem_title": "Time for your glucose check",
        "export_backup": "Export backup (JSON)",
        "import_btn": "Import / Load backup",
        "import_title": "Import data",
        "import_hint": "Pick a .json file (full backup) or a .csv (one profile's export), or type its path below.",
        "import_path_hint": "File path…",
        "import_load": "Load",
        "import_found": "File recognized",
        "import_json_sum": "Backup with %d profile(s), %d reading(s) and %d weight(s).",
        "import_csv_sum": "CSV with %d reading(s) and %d weight(s). It will be added to the active profile: %s.",
        "import_merge": "Merge",
        "import_replace": "Replace all",
        "import_replace_warn": "Merge adds what is missing without deleting anything. Replace overwrites ALL your current data (an automatic copy is saved first).",
        "import_done": "Import complete",
        "import_done_txt": "Profiles: %d · Readings: %d · Weights: %d · Reminders: %d",
        "stats_title": "Period summary",
        "stat_min": "Minimum",
        "stat_max": "Maximum",
        "stat_inrange": "In range (70-140)",
        "stat_out": "High / Low",
        "stat_wchange": "Weight change",
        "bmi_ref": "BMI reference (WHO, adults)",
        "no_weights": "No weights recorded yet.",
        "hist_weight": "Weight",
        "past_weight_btn": "Past weight (Paper)",
        "past_weight_title": "Past weight: date & time 12h",
        "body_prompt": "Enter sex, age, height and weight to calculate BMI.",
    }
}

APP_VERSION = "4.3"
AVISO_VERSION = "1"   # súbela si cambias el aviso legal: se vuelve a pedir la aceptación
AVISO_EXPORT = ("AVISO: registro personal generado por una app creada por un ingeniero en sistemas "
                "(no por un médico). No es un diagnóstico ni sustituye la valoración médica. "
                "Úsalo bajo supervisión médica.")
DEV_NOMBRE = "Ing. Norberto Hernández"

LOGO_CIPHER_PATH = os.path.join(DIR_BASE, "cipher.png")
LOGO_ES_PATH = os.path.join(DIR_BASE, "icon_es.jpg")
LOGO_EN_PATH = os.path.join(DIR_BASE, "icon_eng.jpg")

URL_TELEGRAM = "https://t.me/CipherlosAltos"
URL_BLOG = "https://norbhdz.blogspot.com"
URL_GITHUB = "https://github.com/norbhdz14"
URL_CORREO = "mailto:norbhdz@outlook.com?subject=Reporte%20de%20Error%20Cipher&body=Describe%20tu%20problema%20aqui..."
URL_PAYPAL = "https://paypal.me/norbhdz14"
URL_KOFI = "https://ko-fi.com/cipherlosaltos"


def t(key, lang="es"):
    return TEXTOS.get(lang, TEXTOS["es"]).get(key, key)


def hexa(rgba):
    return "%02x%02x%02x" % tuple(int(c * 255) for c in rgba[:3])


def sin_markup(texto):
    return re.sub(r"\[/?[^\]]*\]", "", texto)


# ----------------------------------------------------------------------
# Android: permiso de notificaciones y guardado en Descargas (MediaStore).
# En Android 10+ ya no se puede escribir con rutas directas en /Download.
# ----------------------------------------------------------------------

MIME_EXPORT = {"csv": "text/csv", "txt": "text/plain", "json": "application/json"}


def pedir_permisos_android():
    """Pide en pantalla el permiso de notificaciones (Android 13+). No hace nada fuera de Android."""
    if platform != "android":
        return
    try:
        from android.permissions import request_permissions
        request_permissions(["android.permission.POST_NOTIFICATIONS"])
    except Exception:
        traceback.print_exc()


def guardar_en_descargas(ruta_origen, nombre, mime):
    """Copia el archivo a la carpeta Descargas con MediaStore (Android 10+).
    Devuelve la ruta que verá el usuario, o None si no se pudo (se usa la carpeta privada)."""
    if platform != "android":
        return None
    entrada = flujo = None
    try:
        from jnius import autoclass
        if autoclass("android.os.Build$VERSION").SDK_INT < 29:
            return None
        activo = autoclass("org.kivy.android.PythonActivity").mActivity
        resolver = activo.getContentResolver()
        columnas = autoclass("android.provider.MediaStore$MediaColumns")
        valores = autoclass("android.content.ContentValues")()
        valores.put(columnas.DISPLAY_NAME, nombre)
        valores.put(columnas.MIME_TYPE, mime)
        valores.put(columnas.RELATIVE_PATH, autoclass("android.os.Environment").DIRECTORY_DOWNLOADS)
        uri = resolver.insert(autoclass("android.provider.MediaStore$Downloads").EXTERNAL_CONTENT_URI, valores)
        if uri is None:
            return None
        flujo = resolver.openOutputStream(uri)
        entrada = autoclass("java.io.FileInputStream")(ruta_origen)
        autoclass("android.os.FileUtils").copy(entrada, flujo)
        return "Download/" + nombre
    except Exception:
        traceback.print_exc()
        return None
    finally:
        for f in (entrada, flujo):
            try:
                if f is not None:
                    f.close()
            except Exception:
                pass


def enviar_notificacion(titulo, mensaje):
    """Intenta una notificación real del sistema con plyer. True si se envió;
    False si plyer no está instalado o el sistema la rechaza (se usa el aviso en pantalla)."""
    try:
        from plyer import notification
        notification.notify(title=str(titulo)[:60], message=str(mensaje)[:240],
                            app_name="Cipher Glucose", timeout=10)
        return True
    except Exception:
        return False


def resumen_compartir(perfil, lang, dias=None, periodo=""):
    """Texto claro (formato WhatsApp) con promedios y últimas lecturas. '' si no hay datos."""
    lect = perfil.lecturas_filtradas(dias)
    if not lect:
        return ""
    vals = [r["valor"] for r in lect]
    prom = sum(vals) / len(vals)
    en_rango = 100.0 * sum(1 for v in vals if RANGO_MIN <= v <= RANGO_MAX) / len(vals)
    nombres = MOMENTOS_ES if lang == "es" else MOMENTOS_EN
    n_lect = t("reading_one", lang) if len(lect) == 1 else t("readings_count", lang)
    L = ["*Cipher Glucose Control*",
         "%s: %s" % (t("wa_profile", lang), perfil.nombre),
         "%s: %s · %d %s" % (t("wa_period", lang), periodo or "—", len(lect), n_lect),
         "%s: %.0f mg/dL · %s %g · %s %g · %s %.0f%%" % (
             t("wa_avg", lang), prom, t("wa_min", lang), min(vals), t("wa_max", lang), max(vals),
             t("wa_inrange", lang), en_rango)]
    pm = promedios_por_momento(lect)
    if pm:
        L += ["", "*%s*" % t("by_moment", lang)]
        for i in sorted(pm):
            L.append("• %s: %.0f mg/dL (%d)" % (nombres[i], pm[i][0], pm[i][1]))
    L += ["", "*%s*" % t("wa_last", lang)]
    for r in reversed(lect[-10:]):
        try:
            fecha = datetime.fromisoformat(r["ts"]).strftime("%d/%m/%y %I:%M %p")
        except ValueError:
            fecha = str(r["ts"])
        mom = nombres[MOMENTO_IDX.get(r.get("momento"), len(nombres) - 1)]
        L.append("• %s · %g mg/dL (%s) · %s" % (fecha, r["valor"], t("st_" + estado_valor(r["valor"]), lang), mom))
    if perfil.tiene_datos_cuerpo:
        imc = perfil.imc_actual
        cat = perfil.categoria_en(imc, perfil.medidas[-1]["ts"])
        L += ["", "%s: %.1f kg · %s %.1f (%s)" % (t("wa_weight", lang), perfil.peso_actual,
                                                   t("bmi", lang), imc, t("bmi_" + cat, lang))]
    L += ["", t("wa_disclaimer", lang)]
    return "\n".join(L)


def mostrar_aviso(titulo, mensaje):
    def _abrir(_dt):
        try:
            caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
            lb = Label(text="[color=%s]%s[/color]" % (hexa(tema_cols()["TEXTO"]), escape_markup(str(mensaje))),
                       markup=True, halign="center", valign="middle",
                       font_size=sp(16) * escala_ui())
            lb.bind(size=lambda inst, s: setattr(inst, "text_size", s))
            btn = boton("OK", CIAN, height=dp(44))
            caja.add_widget(lb)
            caja.add_widget(btn)
            pop = popup_tema(title=titulo, content=caja, size_hint=(0.88, 0.42),
                        separator_color=CIAN, auto_dismiss=True)
            btn.bind(on_release=pop.dismiss)
            pop.open()
        except Exception:
            traceback.print_exc()
    Clock.schedule_once(_abrir, 0)


def registrar_error_en_disco(exc_str, user_dir=""):
    try:
        carpeta = user_dir if user_dir else DIR_BASE
        ruta_reporte = os.path.join(carpeta, "cipher_error_report.txt")
        with open(ruta_reporte, "w", encoding="utf-8") as f:
            f.write("=== REPORTE DE ERROR - CIPHER GLUCOSE ===\n")
            f.write(f"Fecha y Hora: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
            f.write(f"Versión de la App: {APP_VERSION}\n")
            f.write(f"Detalle:\n{exc_str}\n")
            f.write("\nTraceback completo:\n")
            traceback.print_exc(file=f)
        return ruta_reporte
    except Exception:
        return None


def blindado(func):
    @functools.wraps(func)
    def envoltura(*args, **kwargs):
        try:
            return func(*args, **kwargs)
        except ErrorUsuario as exc:
            mostrar_aviso("Aviso", str(exc))
        except Exception as exc:
            traceback.print_exc()
            ruta_rep = registrar_error_en_disco(str(exc))
            msg = f"Ocurrió un error inesperado:\n{exc}\n\n"
            if ruta_rep:
                msg += f"Se generó un informe en:\n{ruta_rep}"
            mostrar_aviso("Error del Sistema", msg)
        return None
    return envoltura


# ----------------------------------------------------------------------
# Ajuste automático de texto: el texto toma el mayor tamaño posible sin salirse
# de su caja (entre un mínimo legible y 1.35x el tamaño nominal).
# ----------------------------------------------------------------------

@functools.lru_cache(maxsize=1024)
def _medida_ref(texto, bold):
    try:
        cl = CoreMarkup(text=texto, font_size=sp(16), bold=bold, markup=True)
        cl.refresh()
        tex = cl.texture
        return tuple(tex.size) if tex else (0, 0)
    except Exception:
        return (0, 0)


def _ajuste_multilinea(texto, bold, aw, ah, nominal, minimo):
    def cabe(fs):
        cl = CoreMarkup(text=texto, font_size=fs, bold=bold, markup=True, text_size=(aw, None))
        cl.refresh()
        tex = cl.texture
        return tex is None or tex.height <= ah
    if cabe(nominal):
        return nominal
    lo, hi, mejor = minimo, nominal, minimo
    for _ in range(6):
        mid = (lo + hi) / 2.0
        if cabe(mid):
            mejor, lo = mid, mid
        else:
            hi = mid
    return mejor


def aplicar_ajuste(w, nominal, multi=False, pad_x=dp(4), pad_y=dp(2), crecer=1.35,
                   texto_attr="text"):
    if CoreMarkup is None:
        return

    def _hacer(*_):
        texto = getattr(w, texto_attr, "") or ""
        aw, ah = w.width - pad_x, w.height - pad_y
        if not texto or aw <= 0 or ah <= 0:
            return
        minimo = sp(9)
        bold = bool(getattr(w, "bold", False))
        try:
            if multi:
                mejor = _ajuste_multilinea(texto, bold, aw, ah, nominal, minimo)
            else:
                w0, h0 = _medida_ref(texto, bold)
                if w0 <= 0 or h0 <= 0:
                    return
                ref = sp(16)
                mejor = min(nominal * crecer, ref * aw / w0, ref * ah / h0) * 0.97
        except Exception:
            return
        mejor = max(minimo, mejor)
        if abs(w.font_size - mejor) > 0.4:
            w.font_size = mejor

    w.bind(size=_hacer)
    w.bind(**{texto_attr: _hacer})
    Clock.schedule_once(_hacer, 0)


def lbl(texto="", **kw):
    ajuste = kw.pop("ajuste", "auto")
    kw.setdefault("color", tema_cols()["TEXTO"])
    kw.setdefault("halign", "left")
    kw.setdefault("valign", "middle")
    kw.setdefault("markup", True)
    if kw.get("shorten"):
        kw.setdefault("shorten_from", "right")
    l = Label(text=texto, **kw)
    l.bind(size=lambda inst, s: setattr(inst, "text_size", s))
    if ajuste:
        aplicar_ajuste(l, kw.get("font_size", sp(15)), multi=(ajuste == "multi"))
    return l


def boton(texto, color=CIAN, factor_escala=1.0, **kw):
    kw.setdefault("size_hint_y", None)
    kw.setdefault("height", dp(48) * k_alto())
    kw.setdefault("font_size", sp(15) * factor_escala)
    b = Button(text=texto, background_normal="", background_down="",
               background_color=color, color=texto_sobre(color),
               bold=True, markup=True, halign="center", valign="middle",
               shorten=True, shorten_from="right", max_lines=1, **kw)
    # el texto nunca se sale de la caja: se recorta con "..."
    b.bind(size=lambda inst, s: setattr(inst, "text_size", (max(0, s[0] - dp(8)), s[1])))
    aplicar_ajuste(b, kw["font_size"], pad_x=dp(12), pad_y=dp(6))
    return b


def campo(**kw):
    kw.setdefault("size_hint_y", None)
    kw.setdefault("height", dp(46) * k_alto())
    kw.setdefault("multiline", False)
    fuente = kw.get("font_size", sp(15))
    kw.setdefault("padding", [dp(10), max(dp(4), (kw["height"] - fuente * 1.3) / 2.0)])
    c = tema_cols()
    claro = c["BG"][0] > 0.5
    kw.setdefault("background_color", (1, 1, 1, 1) if claro else (0.15, 0.20, 0.30, 1))
    kw.setdefault("foreground_color", c["TEXTO"])
    kw.setdefault("hint_text_color", (0.38, 0.43, 0.50, 1) if claro else (0.70, 0.76, 0.84, 1))
    kw.setdefault("cursor_color", (0.0, 0.50, 0.66, 1) if claro else CIAN)
    ti = TextInput(background_normal="", background_active="", write_tab=False, **kw)
    # el texto de ayuda toma el mayor tamaño que cabe; el relleno vertical lo centra
    aplicar_ajuste(ti, fuente, pad_x=dp(26), pad_y=dp(8), crecer=1.2, texto_attr="hint_text")

    def _centrar(*_):
        ti.padding = [dp(10), max(dp(2), (ti.height - ti.font_size * 1.3) / 2.0)]

    ti.bind(size=_centrar, font_size=_centrar)
    return ti


class OpcionSpinner(SpinnerOption):
    # opción de la lista desplegable: letra y alto que siguen el zoom y se ajustan al ancho
    def __init__(self, **kw):
        kw.setdefault("font_size", sp(15) * escala_ui())
        kw.setdefault("size_hint_y", None)
        kw.setdefault("height", dp(46) * k_alto())
        super().__init__(**kw)
        self.halign = "center"
        self.valign = "middle"
        self.shorten = True
        self.shorten_from = "right"
        self.bind(size=lambda i, s: setattr(i, "text_size", (max(0, s[0] - dp(16)), s[1])))
        aplicar_ajuste(self, kw["font_size"], pad_x=dp(20), pad_y=dp(8))


def selector(texto, valores, factor_escala=1.0, **kw):
    kw.setdefault("size_hint_y", None)
    kw.setdefault("height", dp(46) * k_alto())
    kw.setdefault("font_size", sp(13) * factor_escala)
    sp_ = Spinner(text=texto, values=valores, background_normal="",
                  background_down="", background_color=CIAN, color=(0, 0, 0, 1),
                  shorten=True, shorten_from="right", max_lines=1,
                  option_cls=OpcionSpinner, **kw)
    sp_.bind(size=lambda inst, s: setattr(inst, "text_size", (max(0, s[0] - dp(24)), s[1])))
    aplicar_ajuste(sp_, kw["font_size"], pad_x=dp(28), pad_y=dp(6))
    return sp_


class Tarjeta(BoxLayout):
    def __init__(self, color_rgba, **kw):
        super().__init__(**kw)
        with self.canvas.before:
            self._color = Color(*color_rgba)
            self._rect = RoundedRectangle(pos=self.pos, size=self.size,
                                          radius=[dp(12)])
        self.bind(pos=self._act, size=self._act)

    def _act(self, *_):
        self._rect.pos = self.pos
        self._rect.size = self.size

    def set_color(self, rgba):
        self._color.rgba = rgba


# ======================================================================
# 3. GRÁFICA DE TENDENCIA CON SOPORTE DE TEMA Y CONTRASTE
# ======================================================================

class GraficaTendencia(Widget):
    datos = ListProperty([])       # glucosa (modo "gluc": X por índice)
    puntos_g = ListProperty([])    # (tiempo, glucosa)  para modo "ambos"
    puntos_i = ListProperty([])    # (tiempo, IMC, categoría)
    refs_imc = ListProperty([])    # (tiempo, -2DE, +1DE, +2DE) curvas OMS para menores
    modo = StringProperty("gluc")  # "gluc" | "imc" | "ambos"

    def __init__(self, app_ref, **kw):
        super().__init__(**kw)
        self.app_ref = app_ref
        self._ev = None
        self.bind(pos=self._pedir, size=self._pedir, datos=self._pedir,
                  puntos_g=self._pedir, puntos_i=self._pedir, refs_imc=self._pedir, modo=self._pedir)

    def _pedir(self, *_):
        if self._ev is not None:
            self._ev.cancel()
        self._ev = Clock.schedule_once(self._dibujar, 0)

    def _texto(self, txt, x, y, color, derecha=False, centrado=False):
        cl = CoreLabel(text=txt, font_size=sp(12))
        cl.refresh()
        tex = cl.texture
        if tex is None:
            return
        w, h = tex.size
        px = x - w if derecha else (x - w / 2 if centrado else x)
        Color(*color)
        Rectangle(texture=tex, pos=(px, y - h / 2), size=(w, h))

    @blindado
    def _dibujar(self, *_):
        self.canvas.clear()
        modo = self.modo
        ambos = modo == "ambos"
        solo_imc = modo == "imc"
        lang = self.app_ref.idioma_actual
        mi, md, ms, mb = dp(42), (dp(38) if ambos else dp(12)), dp(16), dp(16)
        px, py = self.x + mi, self.y + mb
        pw, ph = self.width - mi - md, self.height - mb - ms
        if pw <= 0 or ph <= 0:
            return
        colores = TEMAS[self.app_ref.tema_actual]

        pi = [(x, v) for x, v, _c in self.puntos_i]
        cats = [c for _x, _v, c in self.puntos_i]
        if modo == "gluc":
            gpts = [(float(i), v) for i, v in enumerate(self.datos)]
            ipts = []
        elif ambos:
            gpts, ipts = list(self.puntos_g), pi
        else:
            gpts, ipts = [], pi

        gvals = [v for _x, v in gpts]
        ivals = [v for _x, v in ipts]
        gmin = min(40, min(gvals) - 10) if gvals else 40
        gmax = max(200, max(gvals) + 10) if gvals else 200
        curvas = list(self.refs_imc) if solo_imc else []
        todos_i = ivals + [v for r in curvas for v in r[1:]]
        imin = min(15.0, min(todos_i) - 1) if todos_i else 15.0
        imax = max(35.0, max(todos_i) + 1) if todos_i else 35.0
        xs = [x for x, _v in gpts + ipts] + [r[0] for r in curvas]
        xmin, xmax = (min(xs), max(xs)) if xs else (0.0, 1.0)

        def xpos(x):
            if xmax <= xmin:
                return px + pw / 2
            return px + (x - xmin) / float(xmax - xmin) * pw

        def yg(v):
            return py + (v - gmin) / float(gmax - gmin) * ph

        def yi(v):
            return py + (v - imin) / float(imax - imin) * ph

        def trazar(pts, yf, col_linea, relleno, color_punto):
            xy = [(xpos(x), yf(v)) for x, v in pts]
            if len(xy) >= 2:
                if relleno:
                    verts = []
                    for (x, y) in xy:
                        verts += [x, y, 0, 0, x, py, 0, 0]
                    Color(col_linea[0], col_linea[1], col_linea[2], 0.20)
                    Mesh(vertices=verts, indices=list(range(len(verts) // 4)),
                         mode="triangle_strip")
                Color(*col_linea)
                Line(points=[c for p in xy for c in p],
                     width=dp(1.8), joint="round", cap="round")
            r = dp(4)
            for k, ((x, y), (_x, v)) in enumerate(zip(xy, pts)):
                Color(*color_punto(v, k))
                Ellipse(pos=(x - r, y - r), size=(2 * r, 2 * r))
            return xy

        with self.canvas:
            Color(*colores["CARD"])
            RoundedRectangle(pos=self.pos, size=self.size, radius=[dp(12)])

            if curvas and len(curvas) >= 2:
                # menores (OMS 5-19 años): banda normal entre -2DE y +1DE y curvas de corte
                banda = []
                for (tt, m2, p1, p2) in curvas:
                    banda += [xpos(tt), yi(m2), 0, 0, xpos(tt), yi(p1), 0, 0]
                Color(0.20, 0.78, 0.44, 0.15)
                Mesh(vertices=banda, indices=list(range(len(banda) // 4)), mode="triangle_strip")
                for idx, col in ((1, colores["AMARILLO"]), (2, colores["AMARILLO"]), (3, ROJO)):
                    Color(col[0], col[1], col[2], 0.9)
                    Line(points=[c for r in curvas for c in (xpos(r[0]), yi(r[idx]))],
                         width=1, dash_length=dp(5), dash_offset=dp(4))
                sd = t("sd_abbr", lang)
                amar = asegurar_contraste(colores["AMARILLO"], colores["CARD"])
                self._texto("-2 %s" % sd, px + dp(4), self.top - dp(9), amar)
                self._texto("+1 %s" % sd, px + dp(52), self.top - dp(9), amar)
                self._texto("+2 %s" % sd, px + dp(100), self.top - dp(9),
                            asegurar_contraste(ROJO, colores["CARD"]))
                for v in (imin, imax):
                    self._texto("%.0f" % v, px - dp(4), yi(v), colores["TEXTO_SUAVE"], derecha=True)
            else:
                refs, yf = ((18.5, 25.0), yi) if solo_imc else ((RANGO_MIN, RANGO_MAX), yg)
                Color(0.20, 0.78, 0.44, 0.15)
                Rectangle(pos=(px, yf(refs[0])), size=(pw, yf(refs[1]) - yf(refs[0])))
                for ref in refs:
                    Color(0.20, 0.78, 0.44, 0.85)
                    Line(points=[px, yf(ref), px + pw, yf(ref)],
                         width=1, dash_length=dp(5), dash_offset=dp(4))
                    self._texto("%g" % ref, px - dp(4), yf(ref), asegurar_contraste(VERDE, colores["CARD"]), derecha=True)

            if ambos:
                for ref in (18.5, 25.0):
                    Color(VIOLETA[0], VIOLETA[1], VIOLETA[2], 0.7)
                    Line(points=[px, yi(ref), px + pw, yi(ref)],
                         width=1, dash_length=dp(2), dash_offset=dp(4))
                    self._texto("%g" % ref, px + pw + dp(4), yi(ref), asegurar_contraste(VIOLETA, colores["CARD"]))

            if not xs:
                self._texto("Sin lecturas / No readings", self.center_x, self.center_y,
                            colores["TEXTO_SUAVE"], centrado=True)
                return

            if gpts:
                xy = trazar(gpts, yg, CIAN, True, lambda v, k: COLOR_ESTADO[estado_valor(v)])
                self._texto("%g" % gvals[-1], xy[-1][0],
                            min(xy[-1][1] + dp(12), self.top - dp(6)),
                            colores["TEXTO"], centrado=True)
            if ipts:
                if solo_imc:
                    def col_i(v, k):
                        return color_cat(cats[k])
                else:
                    def col_i(v, k):
                        return VIOLETA
                xy = trazar(ipts, yi, VIOLETA, solo_imc, col_i)
                self._texto("%.1f" % ivals[-1], xy[-1][0],
                            min(xy[-1][1] + dp(12), self.top - dp(6)) if solo_imc
                            else max(xy[-1][1] - dp(12), self.y + dp(8)),
                            colores["TEXTO"] if solo_imc else asegurar_contraste(VIOLETA, colores["CARD"]), centrado=True)
            if ambos:
                self._texto(t("chart_gluc", lang), px + dp(4), self.top - dp(9), asegurar_contraste(CIAN, colores["CARD"]))
                self._texto(t("chart_bmi", lang), px + dp(70), self.top - dp(9), asegurar_contraste(VIOLETA, colores["CARD"]))


# ======================================================================
# 3b. IDENTIDAD DE MARCA Y LOGOS (Enlazados a Ko-fi)
# ======================================================================

def mezcla(t):
    t = max(0.0, min(1.0, t))
    return tuple(CIAN[i] + (VIOLETA[i] - CIAN[i]) * t for i in range(3)) + (1,)


def texto_degradado(texto, negrita=True):
    n = max(1, len(texto) - 1)
    partes = []
    for i, ch in enumerate(texto):
        if ch == " ":
            partes.append(" ")
        else:
            partes.append("[color=%s]%s[/color]" % (
                hexa(asegurar_contraste(mezcla(i / float(n)), tema_cols()["BG"])), ch))
    s = "".join(partes)
    return "[b]%s[/b]" % s if negrita else s


class LogoCipherCanvas(ButtonBehavior, Widget):
    def __init__(self, **kw):
        super().__init__(**kw)
        self.bind(pos=self._dibujar, size=self._dibujar)
        self._dibujar()

    def on_release(self):
        webbrowser.open(URL_KOFI)

    @staticmethod
    def _engranaje(cx, cy, r_in, r_out, dientes):
        pts, paso = [], 2 * math.pi / dientes
        for i in range(dientes):
            base = i * paso
            for frac, rad in ((0.0, r_in), (0.12, r_out), (0.38, r_out), (0.50, r_in)):
                a = base + frac * paso
                pts.append((cx + rad * math.cos(a), cy + rad * math.sin(a)))
        pts.append(pts[0])
        return pts

    @staticmethod
    def _circulo(cx, cy, r, n=48):
        return [(cx + r * math.cos(2 * math.pi * i / n),
                 cy + r * math.sin(2 * math.pi * i / n)) for i in range(n + 1)]

    @staticmethod
    def _trazo(pts, x0, x1, ancho):
        span = max(1.0, x1 - x0)
        for (ax, ay), (bx, by) in zip(pts, pts[1:]):
            Color(*mezcla(((ax + bx) / 2.0 - x0) / span))
            Line(points=[ax, ay, bx, by], width=ancho, cap="round")

    @blindado
    def _dibujar(self, *_):
        self.canvas.clear()
        u = min(self.width, self.height)
        if u <= 0:
            return
        cx, cy = self.center_x, self.center_y
        R, r_in = 0.35 * u, 0.28 * u
        ancho = max(dp(1.5), u * 0.012)
        x0, x1 = cx - R, cx + R
        with self.canvas:
            Color(1, 1, 1, 0.05)
            Ellipse(pos=(cx - 0.46 * u, cy - 0.46 * u), size=(0.92 * u, 0.92 * u))
            self._trazo(self._engranaje(cx, cy, r_in, R, 8), x0, x1, ancho)
            self._trazo(self._circulo(cx, cy, 0.15 * u), x0, x1, ancho)


class LogoImagenEnlazada(ButtonBehavior, Image):
    def on_release(self):
        webbrowser.open(URL_KOFI)


def obtener_logo_cipher(altura=dp(170)):
    if os.path.exists(LOGO_CIPHER_PATH):
        try:
            return LogoImagenEnlazada(source=LOGO_CIPHER_PATH, size_hint_y=None, height=altura, allow_stretch=True, keep_ratio=True)
        except Exception:
            pass
    return LogoCipherCanvas(size_hint_y=None, height=altura)


def obtener_logo_principal(lang, app_ref, altura=dp(120)):
    contenedor = BoxLayout(size_hint_y=None, height=altura, spacing=dp(10))

    ruta = LOGO_ES_PATH if lang == "es" else LOGO_EN_PATH
    if os.path.exists(ruta):
        try:
            img = LogoImagenEnlazada(source=ruta, size_hint_x=0.56, allow_stretch=True, keep_ratio=True)
            contenedor.add_widget(img)
        except Exception:
            contenedor.add_widget(LogoCipherCanvas(size_hint_x=0.56))
    else:
        contenedor.add_widget(LogoCipherCanvas(size_hint_x=0.56))

    colores = TEMAS[app_ref.tema_actual]
    fs = app_ref.factor_escala_global
    card = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(6),
                   spacing=dp(1), size_hint_x=0.44)
    card.add_widget(lbl(ico("barcode") + t("strips", lang), font_size=sp(14) * fs,
                        color=colores["TEXTO_SUAVE"], shorten=True,
                        size_hint_y=None, height=dp(20)))

    perfil = app_ref.gestor.activo if hasattr(app_ref, "gestor") else None
    fila_num = BoxLayout(spacing=dp(4))
    lb_tiras = lbl("[b]%s[/b]" % (perfil.tiras if perfil else TIRAS_INICIALES),
                   font_size=sp(18) * fs, color=colores["TEXTO"], shorten=True,
                   size_hint_x=0.46)
    lb_prom_logo = lbl("—", font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"],
                       halign="right", shorten=True, shorten_from="left",
                       size_hint_x=0.54)
    fila_num.add_widget(lb_tiras)
    fila_num.add_widget(lb_prom_logo)
    card.add_widget(fila_num)

    app_ref.lb_tiras_logo = lb_tiras
    app_ref.lb_prom_logo = lb_prom_logo
    app_ref.card_tiras_logo = card

    btn_add = boton(ico("mas") + t("add_strips", lang), AZUL, factor_escala=fs,
                    size_hint_y=None, height=dp(24), font_size=sp(12) * fs)
    btn_add.bind(on_release=lambda *_: app_ref.raiz_ref._popup_tiras())
    card.add_widget(btn_add)

    # IMC: toca para registrar o actualizar sexo, estatura y peso
    btn_imc = boton(ico("mas") + t("bmi", lang), VIOLETA, factor_escala=fs,
                    size_hint_y=None, height=dp(24), font_size=sp(12) * fs)
    btn_imc.bind(on_release=lambda *_: app_ref.raiz_ref._popup_cuerpo())
    card.add_widget(btn_imc)
    app_ref.btn_imc_logo = btn_imc

    contenedor.add_widget(card)
    return contenedor


def _btn_enlace(texto, url, nombre, color, factor_escala=1.0, **kw):
    b = boton(texto, color if url else (0.3, 0.3, 0.3, 1), factor_escala=factor_escala, **kw)
    b.bind(on_release=lambda *_: webbrowser.open(url) if url else mostrar_aviso(nombre, "Enlace no configurado"))
    return b


def abrir_acerca_de(app_ref):
    lang = app_ref.idioma_actual
    fs = app_ref.factor_escala_global
    claro = app_ref.tema_actual == "light"
    col_suave = TEMAS[app_ref.tema_actual]["TEXTO_SUAVE"]
    col_card = TEMAS[app_ref.tema_actual]["CARD"]
    cont = GridLayout(cols=1, spacing=dp(10), size_hint_y=None,
                      padding=[dp(4), dp(4), dp(4), dp(10)])
    cont.bind(minimum_height=cont.setter("height"))

    cont.add_widget(obtener_logo_cipher(dp(170)))
    cont.add_widget(lbl(texto_degradado("Cipher"), font_size=sp(34) * fs,
                        halign="center", size_hint_y=None, height=dp(52)))
    cont.add_widget(lbl(ico("llave") + t("dev_role", lang),
                        font_size=sp(13) * fs, halign="center", color=col_suave,
                        size_hint_y=None, height=dp(24), shorten=True))

    t_app = Tarjeta(col_card, orientation="vertical", padding=dp(12), spacing=dp(4),
                    size_hint_y=None, height=dp(130))
    t_app.add_widget(lbl(texto_degradado(t("app_title", lang)) + " v%s" % APP_VERSION,
                         font_size=sp(14) * fs, size_hint_y=None, height=dp(26), shorten=True))
    t_app.add_widget(lbl(
        "Control de glucosa con perfiles, inventario, gráfica y exportación. Herramienta personal."
        if lang == "es" else "Glucose tracking with profiles, inventory, charts and export. Personal tool.",
        font_size=sp(12) * fs, color=col_suave, valign="top", ajuste="multi"))
    cont.add_widget(t_app)

    t_dev = Tarjeta(col_card, orientation="vertical", padding=dp(12), spacing=dp(2),
                    size_hint_y=None, height=dp(115))
    t_dev.add_widget(lbl(texto_degradado(t("dev_section", lang)), font_size=sp(13) * fs,
                         size_hint_y=None, height=dp(24), shorten=True))
    t_dev.add_widget(lbl(ico("usuario") + "[b]%s[/b]" % DEV_NOMBRE, font_size=sp(15) * fs,
                         size_hint_y=None, height=dp(26), shorten=True))
    t_dev.add_widget(lbl(t("cedula", lang), font_size=sp(12) * fs,
                         color=col_suave, size_hint_y=None, height=dp(22), shorten=True))
    t_dev.add_widget(lbl(ico("pin") + "Arandas, Jalisco", font_size=sp(12) * fs,
                         color=col_suave, shorten=True))
    cont.add_widget(t_dev)

    t_ded = Tarjeta(col_card, orientation="vertical", padding=dp(12), spacing=dp(4),
                    size_hint_y=None, height=dp(190))
    t_ded.add_widget(lbl(ico("corazon") + texto_degradado(t("dedic_title", lang)), font_size=sp(14) * fs,
                         size_hint_y=None, height=dp(26), shorten=True))
    t_ded.add_widget(lbl(t("dedic_text", lang), font_size=sp(13) * fs, color=col_suave,
                         valign="top", ajuste="multi"))
    cont.add_widget(t_ded)

    t_aviso = Tarjeta(TEMAS[app_ref.tema_actual]["ROJO_OSCURO"], orientation="vertical",
                      padding=dp(10), size_hint_y=None, height=dp(88))
    t_aviso.add_widget(lbl(ico("aviso") + t("disc_short", lang), font_size=sp(12) * fs,
                           color=TEMAS[app_ref.tema_actual]["TEXTO"], valign="top", ajuste="multi"))
    cont.add_widget(t_aviso)

    cont.add_widget(lbl(texto_degradado(t("contact_support", lang)), font_size=sp(14) * fs,
                        size_hint_y=None, height=dp(26), shorten=True))
    grid = GridLayout(cols=2, spacing=dp(8), size_hint_y=None)
    grid.bind(minimum_height=grid.setter("height"))
    grid.add_widget(_btn_enlace(ico("telegram") + "Telegram", URL_TELEGRAM, "Telegram", AZUL, factor_escala=fs, height=dp(48)))
    grid.add_widget(_btn_enlace(ico("globo") + "Blog", URL_BLOG, "Blog", CIAN, factor_escala=fs, height=dp(48)))
    grid.add_widget(_btn_enlace(ico("codigo") + "GitHub", URL_GITHUB, "GitHub", VIOLETA, factor_escala=fs, height=dp(48)))
    grid.add_widget(_btn_enlace(ico("correo") + "Correo", URL_CORREO, "Correo", AZUL, factor_escala=fs, height=dp(48)))
    cont.add_widget(grid)

    btn_reporte = boton(ico("aviso") + t("report_error", lang), ROJO, factor_escala=fs, height=dp(46))
    btn_reporte.bind(on_release=lambda *_: webbrowser.open(URL_CORREO))
    cont.add_widget(btn_reporte)

    cont.add_widget(lbl(texto_degradado(t("support_project", lang)), font_size=sp(14) * fs,
                        size_hint_y=None, height=dp(26), shorten=True))
    cont.add_widget(lbl(t("support_desc", lang), font_size=sp(12) * fs,
                        color=col_suave, valign="top", ajuste="multi",
                        size_hint_y=None, height=dp(44)))
    fila_apoyo = BoxLayout(size_hint_y=None, height=dp(52), spacing=dp(8))
    fila_apoyo.add_widget(_btn_enlace(ico("corazon") + "Ko-fi", URL_KOFI, "Ko-fi", VIOLETA, factor_escala=fs, height=dp(52)))
    fila_apoyo.add_widget(_btn_enlace(ico("paypal") + "PayPal", URL_PAYPAL, "PayPal", AZUL, factor_escala=fs, height=dp(52)))
    cont.add_widget(fila_apoyo)

    scroll = ScrollView(do_scroll_x=False, bar_width=dp(3))
    scroll.add_widget(cont)
    raiz = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(6))
    raiz.add_widget(scroll)
    b_cerrar = boton(ico("cerrar") + t("close", lang), CIAN, factor_escala=fs, height=dp(48))
    raiz.add_widget(b_cerrar)
    pop = popup_tema(title=t("about_popup_title", lang), content=raiz, size_hint=(0.95, 0.90),
                separator_color=VIOLETA)
    b_cerrar.bind(on_release=pop.dismiss)
    pop.open()


# ======================================================================
# 4. PANTALLA PRINCIPAL
# ======================================================================

def _texto_largo(texto, fs, color):
    # etiqueta de varias líneas que crece según su contenido
    lb = Label(text=texto, markup=True, color=color, font_size=sp(13) * fs,
               halign="left", valign="top", size_hint_y=None)
    lb.bind(width=lambda w, v: setattr(w, "text_size", (max(0, v - dp(12)), None)))
    lb.bind(texture_size=lambda w, ts: setattr(w, "height", ts[1] + dp(14)))
    return lb


def ayuda_secciones(lang):
    c = tema_cols()

    def pto(col):
        return "[color=%s]%s[/color]" % (hexa(col_t(col, c["BG"])), ico("circulo") or "●")

    ver, rojo, amar = pto(VERDE), pto(ROJO), pto(c["AMARILLO"])
    if lang == "es":
        return [
            ("aviso", ROJO, "Aviso importante", t("disc_text", "es")),
            ("usuario", VIOLETA, "Primeros pasos",
             "[b]1.[/b] Toca [b]+ Usuario[/b] y escribe un nombre. Cada persona tiene su propio perfil.\n"
             "[b]2.[/b] Completa [b]sexo, edad, estatura y peso[/b] (botón IMC de la parte superior).\n"
             "[b]3.[/b] En la pestaña [b]Glucosa[/b] escribe el valor, elige el momento (en ayunas, antes de comer…) "
             "y toca [b]Registrar lectura[/b].\n"
             "[b]4.[/b] Revisa [b]Estadísticas[/b] e [b]Historial[/b] y llévalos a tu consulta (exporta CSV o TXT)."),
            ("lupa", NARANJA, "Zoom y pantallas grandes",
             "• El botón naranja [b]Zoom[/b] de la barra superior muestra el nivel actual (por ejemplo 150%) y, cada vez que "
             "lo tocas, pasa al siguiente: [b]125%, 150%, 175%, 200%, 225% y 250%[/b]; después de 250% vuelve a 125%.\n"
             "• Con zoom alto, los textos largos se acortan con “…” y los botones se hacen más altos. Si algo no cabe, "
             "desplázate hacia abajo.\n"
             "• La app recuerda el nivel que elegiste.\n"
             "• [b]Tableta o computadora[/b]: en pantallas anchas la app se acomoda sola en [b]dos columnas[/b]. A la izquierda "
             "están tu perfil, las tiras, el formulario de Glucosa y el IMC; a la derecha, Estadísticas e Historial. "
             "En el celular se mantiene en una sola columna. Al girar el teléfono a horizontal también puede cambiar."),
            ("gota", CIAN, "Glucosa",
             "• Escribe la glucosa en [b]mg/dL[/b] (la app acepta de 20 a 600).\n"
             "• [b]Momento[/b]: indica si fue en ayunas, antes de comer, etc. Ayuda a tu médico a interpretar el dato.\n"
             "• [b]Lectura pasada (Papel)[/b]: registra una medición anotada en papel con su fecha y hora reales. "
             "No acepta fechas futuras.\n"
             "• Cada lectura descuenta una tira reactiva del contador.\n"
             "• [b]Colores[/b] (referencia general de 70 a 140 mg/dL):\n"
             + ver + " normal     " + rojo + " fuera de rango (baja o alta)\n"
             "Es una referencia de la app, [b]no tu meta personal[/b]: tu médico puede indicarte otra."),
            ("campana", AZUL, "Recordatorios",
             "• Guarda horarios de comidas. Cada uno se activa con ON/OFF y se elimina con el botón de papelera.\n"
             "• [b]Notificaciones[/b]: al activar un recordatorio y a la hora indicada, la app intenta lanzar una "
             "notificación del teléfono (necesita la librería [b]plyer[/b] y el permiso de notificaciones). "
             "Si no está disponible, muestra un aviso dentro de la app.\n"
             "• [b]Importante:[/b] solo avisa mientras la app esté abierta; si la cierras o Android la detiene, no sonará. "
             "Usa también la alarma de tu reloj o teléfono para no olvidar tus controles."),
            ("barcode", AZUL, "Tiras reactivas",
             "• El número junto a TIRAS es lo que te queda; baja 1 con cada lectura.\n"
             "• " + amar + " [b]15 o menos[/b]: se acabarán pronto.   " + rojo + " [b]10 o menos[/b]: hay que reponer.\n"
             "• [b]+ Añadir[/b] suma tiras nuevas. [b]Fijar total[/b] corrige la cantidad exacta."),
            ("peso", VIOLETA, "Peso e IMC",
             "• IMC = peso (kg) ÷ estatura (m) al cuadrado.\n"
             "• [b]Adultos (19 años o más)[/b], según la OMS: bajo peso menos de 18.5 · normal 18.5 a 24.9 · "
             "sobrepeso 25 a 29.9 · obesidad 30 o más.\n"
             "• [b]De 5 a 18 años[/b]: la OMS no usa esos números fijos. Compara el IMC con el de niños de la misma "
             "[b]edad y sexo[/b] (referencia OMS 2007): delgadez por debajo de -2 DE, sobrepeso por encima de +1 DE "
             "y obesidad por encima de +2 DE (DE = desviaciones estándar).\n"
             "• [b]Menores de 5 años[/b]: la OMS usa otras tablas (peso para la talla) que la app aún no incluye.\n"
             "• El IMC es solo una orientación: no distingue músculo de grasa y no sustituye la valoración de tu médico.\n"
             "• Registra tu peso con [b]Registrar peso[/b], o con [b]Peso pasado (Papel)[/b] si lo anotaste antes."),
            ("grafica", CIAN, "Estadísticas",
             "• [b]Promedio[/b] y número de lecturas del periodo elegido (todo, 1 semana… 3 meses).\n"
             "• [b]Resumen[/b]: mínimo, máximo, porcentaje en rango, altas y bajas, y cambio de peso.\n"
             "• [b]Gráfica[/b]: alterna entre Glucosa e IMC. En menores se dibujan las curvas de la OMS.\n"
             "• [b]Promedio por momento del día[/b]: separa tu glucosa en ayunas, antes de comer, postprandial, etc., con el "
             "número de lecturas de cada uno. Los tres momentos principales aparecen siempre (con “—” si no hay datos). "
             "Sirve para tu consulta: tu médico decide cómo interpretarlo."),
            ("lista", AZUL, "Historial y exportar",
             "• Muestra tus últimas 50 lecturas o pesos.\n"
             "• [b]Exportar CSV o TXT[/b] guarda un archivo en Descargas para compartirlo con tu médico. "
             "El TXT incluye un aviso de uso.\n"
             "• [b]Compartir por WhatsApp[/b] abre WhatsApp con un resumen (promedio, mínimo, máximo, porcentaje en rango, "
             "promedio por momento y las últimas 10 lecturas) para que elijas a quién enviarlo. Revísalo antes de "
             "enviar: contiene datos de salud. Si WhatsApp no abre, el resumen se copia para que lo pegues."),
            ("respaldo", VERDE, "Respaldo e importación",
             "• [b]Exportar respaldo (JSON)[/b] guarda en Descargas una copia de [b]todos[/b] los perfiles: lecturas, pesos, "
             "tiras y recordatorios.\n"
             "• Para cambiar de teléfono: copia ese archivo al teléfono nuevo, abre [b]Importar / Cargar respaldo[/b] en la "
             "pestaña Historial y elígelo (o escribe su ruta).\n"
             "• [b]Fusionar[/b] agrega lo que falte sin borrar nada y sin duplicar lecturas ya existentes. "
             "[b]Reemplazar todo[/b] sustituye tus datos actuales por los del archivo; antes se guarda una copia automática.\n"
             "• También puedes cargar un [b]CSV[/b] exportado de un perfil: se agrega al perfil activo.\n"
             "• Importa solo archivos que tú exportaste o que te dio alguien de confianza. La app revisa el contenido y "
             "descarta los datos no válidos."),
            ("candado", VERDE, "Privacidad y respaldo",
             "• Tus datos se guardan [b]solo en este teléfono[/b]. La app no los envía a ningún servidor.\n"
             "• Si desinstalas la app o borras sus datos, [b]se pierden[/b]. Exporta copias con frecuencia.\n"
             "• Los botones de Soporte (Telegram, correo…) abren tu navegador o la app correspondiente."),
            ("globo", AZUL, "Lo que dice la OMS",
             "• La diabetes es una enfermedad crónica: el páncreas no produce suficiente insulina o el cuerpo no la "
             "usa bien.\n"
             "• Una alimentación saludable, la actividad física regular, mantener un peso normal y no fumar ayudan a "
             "prevenir o retrasar la diabetes tipo 2.\n"
             "• Alimentación: más frutas y verduras, y menos azúcar y grasas saturadas.\n"
             "• Actividad física: en adultos, al menos 30 minutos de actividad moderada la mayoría de los días "
             "(unos 150 minutos por semana); en niños y adolescentes, en promedio 60 minutos al día.\n"
             "• El tratamiento busca controlar la glucosa y otros factores de riesgo; el diagnóstico se confirma "
             "con análisis de laboratorio.\n"
             "• El control regular ayuda a detectar a tiempo complicaciones (corazón, riñón, vista, pies).\n"
             "• Fumar aumenta el riesgo de diabetes y de enfermedad cardiovascular.\n"
             "Fuentes: hojas informativas de la OMS sobre diabetes y la referencia OMS de crecimiento para 5 a 19 años (2007)."),
            ("medico", ROJO, "Cuándo buscar ayuda",
             "• Sigue siempre el plan que te dio tu médico para valores bajos o altos.\n"
             "• Si hay [b]confusión, desmayo, convulsiones o dificultad para respirar[/b], o crees que es una "
             "emergencia, llama a tu número local de emergencias (en México, 911).\n"
             "• Consulta a tu médico antes de cambiar medicamentos, dosis, dieta o ejercicio. La app no calcula dosis.\n"
             "• Si una lectura te parece rara, repítela y revisa tu glucómetro y tus tiras."),
        ]
    return [
        ("aviso", ROJO, "Important notice", t("disc_text", "en")),
        ("usuario", VIOLETA, "Getting started",
         "[b]1.[/b] Tap [b]+ User[/b] and type a name. Each person has their own profile.\n"
         "[b]2.[/b] Fill in [b]sex, age, height and weight[/b] (BMI button at the top).\n"
         "[b]3.[/b] In the [b]Glucose[/b] tab type the value, pick the moment (fasting, before meal…) "
         "and tap [b]Register reading[/b].\n"
         "[b]4.[/b] Check [b]Stats[/b] and [b]History[/b] and bring them to your appointment (export CSV or TXT)."),
        ("lupa", NARANJA, "Zoom and large screens",
         "• The orange [b]Zoom[/b] button in the top bar shows the current level (for example 150%) and moves to the "
         "next one each time you tap it: [b]125%, 150%, 175%, 200%, 225% and 250%[/b]; after 250% it goes back to 125%.\n"
         "• With high zoom, long texts are shortened with “…” and buttons get taller. If something does not fit, scroll down.\n"
         "• The app remembers the level you chose.\n"
         "• [b]Tablet or computer[/b]: on wide screens the app arranges itself in [b]two columns[/b]. On the left are your "
         "profile, strips, the Glucose form and BMI; on the right, Stats and History. On a phone it stays in one column. "
         "Rotating the phone sideways can also switch the layout."),
        ("gota", CIAN, "Glucose",
         "• Enter glucose in [b]mg/dL[/b] (the app accepts 20 to 600).\n"
         "• [b]Moment[/b]: fasting, before a meal, etc. It helps your doctor interpret the value.\n"
         "• [b]Past reading (Paper)[/b]: log a paper measurement with its real date and time. Future dates are not accepted.\n"
         "• Each reading uses up one test strip from the counter.\n"
         "• [b]Colors[/b] (general reference of 70 to 140 mg/dL):\n"
         + ver + " normal     " + rojo + " out of range (low or high)\n"
         "It is an app reference, [b]not your personal target[/b]: your doctor may give you another."),
        ("campana", AZUL, "Reminders",
         "• Save meal times. Each one is switched with ON/OFF and removed with the trash button.\n"
         "• [b]Notifications[/b]: when you turn a reminder on and at the set time, the app tries to send a phone "
         "notification (it needs the [b]plyer[/b] library and notification permission). "
         "If unavailable, it shows an alert inside the app.\n"
         "• [b]Important:[/b] it only alerts while the app is open; if you close it or Android stops it, it will not ring. "
         "Also use your watch or phone alarm so you do not miss your checks."),
        ("barcode", AZUL, "Test strips",
         "• The number next to STRIPS is what you have left; it drops by 1 with each reading.\n"
         "• " + amar + " [b]15 or fewer[/b]: running out soon.   " + rojo + " [b]10 or fewer[/b]: time to restock.\n"
         "• [b]+ Add[/b] adds new strips. [b]Set total[/b] corrects the exact amount."),
        ("peso", VIOLETA, "Weight & BMI",
         "• BMI = weight (kg) ÷ height (m) squared.\n"
         "• [b]Adults (19 or older)[/b], per WHO: underweight below 18.5 · normal 18.5 to 24.9 · "
         "overweight 25 to 29.9 · obesity 30 or more.\n"
         "• [b]Ages 5 to 18[/b]: WHO does not use those fixed numbers. It compares BMI with children of the same "
         "[b]age and sex[/b] (WHO 2007 reference): thinness below -2 SD, overweight above +1 SD and obesity above "
         "+2 SD (SD = standard deviations).\n"
         "• [b]Under 5 years[/b]: WHO uses other tables (weight-for-height) that the app does not include yet.\n"
         "• BMI is only guidance: it does not tell muscle from fat and does not replace your doctor's assessment.\n"
         "• Log your weight with [b]Log weight[/b], or [b]Past weight (Paper)[/b] if you wrote it down earlier."),
        ("grafica", CIAN, "Stats",
         "• [b]Average[/b] and number of readings for the chosen period (all, 1 week… 3 months).\n"
         "• [b]Summary[/b]: minimum, maximum, percentage in range, highs and lows, and weight change.\n"
         "• [b]Chart[/b]: switch between Glucose and BMI. For minors the WHO curves are drawn.\n"
         "• [b]Average by time of day[/b]: splits your glucose into fasting, before meal, postprandial, etc., with the "
         "number of readings in each. The three main moments always show (with “—” if there is no data). "
         "Useful for your appointment: your doctor decides how to interpret it."),
        ("lista", AZUL, "History & export",
         "• Shows your last 50 readings or weights.\n"
         "• [b]Export CSV or TXT[/b] saves a file in Downloads to share with your doctor. The TXT includes a use notice.\n"
         "• [b]Share via WhatsApp[/b] opens WhatsApp with a summary (average, min, max, percent in range, "
         "average by time of day and the last 10 readings) so you choose who gets it. Review it before "
         "sending: it contains health data. If WhatsApp does not open, the summary is copied so you can paste it."),
        ("respaldo", VERDE, "Backup and import",
         "• [b]Export backup (JSON)[/b] saves a copy of [b]all[/b] profiles in Downloads: readings, weights, strips and reminders.\n"
         "• To switch phones: copy that file to the new phone, open [b]Import / Load backup[/b] in the History tab and pick it "
         "(or type its path).\n"
         "• [b]Merge[/b] adds what is missing without deleting anything or duplicating existing readings. "
         "[b]Replace all[/b] overwrites your current data with the file's; an automatic copy is saved first.\n"
         "• You can also load a [b]CSV[/b] exported from one profile: it is added to the active profile.\n"
         "• Only import files you exported yourself or that someone you trust gave you. The app checks the content and "
         "discards invalid data."),
        ("candado", VERDE, "Privacy & backup",
         "• Your data is stored [b]only on this phone[/b]. The app does not send it to any server.\n"
         "• If you uninstall the app or clear its data, [b]it is lost[/b]. Export copies often.\n"
         "• Support buttons (Telegram, email…) open your browser or the matching app."),
        ("globo", AZUL, "What WHO says",
         "• Diabetes is a chronic disease: the pancreas does not make enough insulin or the body cannot use it well.\n"
         "• A healthy diet, regular physical activity, a normal body weight and not smoking help prevent or delay "
         "type 2 diabetes.\n"
         "• Diet: more fruit and vegetables, less sugar and saturated fat.\n"
         "• Physical activity: adults, at least 30 minutes of moderate activity on most days (about 150 minutes a "
         "week); children and adolescents, an average of 60 minutes a day.\n"
         "• Treatment aims to control glucose and other risk factors; diagnosis is confirmed with laboratory tests.\n"
         "• Regular check-ups help catch complications early (heart, kidney, eyes, feet).\n"
         "• Smoking raises the risk of diabetes and cardiovascular disease.\n"
         "Sources: WHO diabetes fact sheets and the WHO growth reference for 5 to 19 years (2007)."),
        ("medico", ROJO, "When to seek help",
         "• Always follow the plan your doctor gave you for low or high values.\n"
         "• If there is [b]confusion, fainting, seizures or trouble breathing[/b], or you think it is an emergency, "
         "call your local emergency number.\n"
         "• Talk to your doctor before changing medication, doses, diet or exercise. The app does not calculate doses.\n"
         "• If a reading looks odd, repeat it and check your meter and strips."),
    ]


def abrir_ayuda(app_ref):
    lang = app_ref.idioma_actual
    fs = app_ref.factor_escala_global
    c = TEMAS[app_ref.tema_actual]
    cont = GridLayout(cols=1, spacing=dp(8), size_hint_y=None, padding=[dp(4), dp(4), dp(4), dp(10)])
    cont.bind(minimum_height=cont.setter("height"))
    cont.add_widget(lbl(ico("info") + texto_degradado(t("help_title", lang)), font_size=sp(20) * fs,
                        size_hint_y=None, height=dp(34), shorten=True))
    cont.add_widget(lbl(t("help_intro", lang), font_size=sp(12) * fs, color=c["TEXTO_SUAVE"],
                        size_hint_y=None, height=dp(22), shorten=True))

    for i, (icono, col, titulo, cuerpo) in enumerate(ayuda_secciones(lang)):
        bloque = GridLayout(cols=1, size_hint_y=None, spacing=dp(2))
        bloque.bind(minimum_height=bloque.setter("height"))
        cab = boton("", col, factor_escala=fs, height=dp(44), font_size=sp(13) * fs)
        texto = _texto_largo(cuerpo, fs, c["TEXTO"])
        estado = {"abierto": False}

        def poner(abierto, cab=cab, bloque=bloque, texto=texto, icono=icono, titulo=titulo, estado=estado):
            estado["abierto"] = abierto
            cab.text = ico("chev_d" if abierto else "chev_r") + ico(icono) + titulo
            if abierto and texto.parent is None:
                bloque.add_widget(texto)
            elif not abierto and texto.parent is not None:
                bloque.remove_widget(texto)

        def alternar(_b, poner=poner, estado=estado):
            poner(not estado["abierto"])

        cab.bind(on_release=alternar)
        bloque.add_widget(cab)
        poner(i == 0)
        cont.add_widget(bloque)

    scroll = ScrollView(do_scroll_x=False, bar_width=dp(3))
    scroll.add_widget(cont)
    raiz = BoxLayout(orientation="vertical", spacing=dp(8), padding=dp(6))
    raiz.add_widget(scroll)
    b_cerrar = boton(ico("cerrar") + t("close", lang), CIAN, factor_escala=fs, height=dp(48))
    raiz.add_widget(b_cerrar)
    pop = popup_tema(title=t("help_title", lang), content=raiz, size_hint=(0.95, 0.92),
                     separator_color=VERDE)
    b_cerrar.bind(on_release=pop.dismiss)
    pop.open()


class PantallaPrincipal(BoxLayout):

    def __init__(self, gestor, app, **kw):
        super().__init__(orientation="vertical", padding=dp(10),
                         spacing=dp(8), **kw)
        self.gestor = gestor
        self.app = app
        self.app.raiz_ref = self
        self._actualizando = False
        self._idx_periodo = 0
        self._idx_modo = 0
        self._idx_hist = 0
        self._tab_actual = "gluc"
        self._tab_izq = "gluc"
        self._tab_der = "stats"
        self._ancho = None
        self._avisados = set()

        with self.canvas.before:
            Color(*TEMAS[self.app.tema_actual]["BG"])
            self._fondo = Rectangle(pos=self.pos, size=self.size)
        self.bind(pos=self._act_fondo, size=self._act_fondo)

        self._construir()
        self.refrescar()

        Clock.schedule_interval(self._actualizar_reloj, 1.0)
        Clock.schedule_once(self._arranque, 0.6)
        Clock.schedule_interval(self._revisar_recordatorios, 15)
        Window.bind(size=self._on_ventana)

    def _act_fondo(self, *_):
        self._fondo.pos = self.pos
        self._fondo.size = self.size

    def actualizar_estilos(self):
        # conserva lo que el usuario ya había escrito al cambiar tema/idioma/zoom
        v = self.txt_valor.text
        n = self.txt_notas.text
        colores = TEMAS[self.app.tema_actual]
        Window.clearcolor = colores["BG"]
        self.canvas.before.clear()
        with self.canvas.before:
            Color(*colores["BG"])
            self._fondo = Rectangle(pos=self.pos, size=self.size)
        self.clear_widgets()
        self._construir()
        self.txt_valor.text = v
        self.txt_notas.text = n
        self.refrescar()

    def _construir(self):
        lang = self.app.idioma_actual
        colores = TEMAS[self.app.tema_actual]
        fs = self.app.factor_escala_global
        fb = sp(12) * fs

        ka = k_alto()
        prev = getattr(self, "_ancho", None)
        self._ancho = self._es_ancho()
        if prev is not None and prev != self._ancho and self._ancho:
            if self._tab_actual in ("gluc", "imc"):
                self._tab_izq = self._tab_actual
            else:
                self._tab_der = self._tab_actual

        top_bar = BoxLayout(size_hint_y=None, height=dp(44) * ka, spacing=dp(4))

        oscuro = self.app.tema_actual == "dark"
        self.btn_tema = boton(ico("luna" if oscuro else "sol") +
                              t("theme_dark" if oscuro else "theme_light", lang),
                              (0.2, 0.3, 0.4, 1), size_hint_x=0.16, height=dp(44) * ka, font_size=fb)
        self.btn_tema.bind(on_release=self._alternar_tema_directo)

        self.btn_lang = boton(ico("globo") + ("ES" if lang == "es" else "ENG"),
                              (0.2, 0.3, 0.4, 1), size_hint_x=0.12, height=dp(44) * ka, font_size=fb)
        self.btn_lang.bind(on_release=self._alternar_lang_directo)

        self.btn_reloj = boton(ico("reloj") + "00:00", (0.2, 0.25, 0.35, 1),
                               size_hint_x=0.18, height=dp(44) * ka, font_size=fb)
        self.btn_reloj.bind(on_release=self._alternar_formato_reloj)

        # zoom: botón naranja que muestra el nivel actual (p. ej. "Zoom 150%")
        btn_lupa = boton(ico("lupa") + "Zoom %d%%" % round(fs * 100), NARANJA, size_hint_x=0.22,
                         height=dp(44) * ka, font_size=fb)
        btn_lupa.bind(on_release=lambda *_: self.app.ciclar_zoom())

        btn_about = boton(ico("ayuda") + t("about", lang), CIAN, size_hint_x=0.20,
                          height=dp(44) * ka, font_size=fb)
        btn_about.bind(on_release=lambda *_: abrir_acerca_de(self.app))

        btn_ayuda = boton(ico("info", espacio=False) or "?", VERDE, size_hint_x=0.12,
                          height=dp(44) * ka, font_size=sp(14) * fs)
        btn_ayuda.bind(on_release=lambda *_: abrir_ayuda(self.app))

        for w in (self.btn_tema, self.btn_lang, self.btn_reloj, btn_lupa, btn_about, btn_ayuda):
            top_bar.add_widget(w)

        self.logo_contenedor = obtener_logo_principal(lang, self.app, dp(120) * (1 + (ka - 1) * 0.5))

        barra = BoxLayout(size_hint_y=None, height=dp(46) * ka, spacing=dp(8))
        self.spn_perfil = selector("", [], factor_escala=fs, size_hint_x=0.68)
        self.spn_perfil.bind(text=self._on_cambio_perfil)
        btn_nuevo = boton(ico("usuario") + t("new_user", lang), VIOLETA, factor_escala=fs, size_hint_x=0.32)
        btn_nuevo.bind(on_release=lambda *_: self._popup_nuevo_perfil())
        barra.add_widget(self.spn_perfil)
        barra.add_widget(btn_nuevo)

        # ---------------- PESTAÑAS ----------------
        self._botones_tab = {}
        for clave, ic_, k in (("gluc", "gota", "tab_gluc"), ("imc", "peso", "tab_bmi"),
                              ("stats", "grafica", "tab_stats"), ("hist", "lista", "tab_hist")):
            b = boton(ico(ic_) + t(k, lang), (0.2, 0.3, 0.4, 1), factor_escala=fs,
                      height=dp(46) * ka, font_size=sp(13) * fs)
            b.bind(on_release=lambda _b, c=clave: self._mostrar_tab(c))
            self._botones_tab[clave] = b
        self._tabs = {}

        def nueva_pestana(clave):
            sv = ScrollView(do_scroll_x=False, bar_width=dp(3))
            c = GridLayout(cols=1, spacing=dp(10), size_hint_y=None, padding=[0, 0, 0, dp(16)])
            c.bind(minimum_height=c.setter("height"))
            sv.add_widget(c)
            self._tabs[clave] = sv
            return c

        # ================= PESTAÑA GLUCOSA =================
        cont = nueva_pestana("gluc")
        form = Tarjeta(colores["CARD2"], orientation="vertical", padding=dp(12), spacing=dp(10),
                       size_hint_y=None, height=dp(330))

        form.add_widget(lbl("[b][color=%s]" % hexa(col_t(CIAN, colores["CARD2"])) + ico("editar") + t("new_reading", lang).upper() + "[/color][/b]",
                            font_size=sp(14) * fs, size_hint_y=None, height=dp(24), shorten=True))

        fila = BoxLayout(size_hint_y=None, height=dp(50), spacing=dp(8))
        self.txt_valor = campo(hint_text=t("placeholder_val", lang), input_filter="int",
                               input_type="number", size_hint_x=0.34,
                               font_size=sp(16) * fs, height=dp(50))
        self.txt_valor.background_color = (1, 1, 1, 0.95) if not oscuro else (0.15, 0.20, 0.30, 1)
        self.txt_valor.foreground_color = colores["TEXTO"]

        momentos_disp = MOMENTOS_ES if lang == "es" else MOMENTOS_EN
        self.spn_momento = selector(momentos_disp[0], momentos_disp, factor_escala=fs,
                                    size_hint_x=0.66, height=dp(50))

        fila.add_widget(self.txt_valor)
        fila.add_widget(self.spn_momento)
        form.add_widget(fila)

        self.txt_notas = campo(hint_text=t("placeholder_notes", lang), font_size=sp(13) * fs)
        self.txt_notas.background_color = (1, 1, 1, 0.95) if not oscuro else (0.15, 0.20, 0.30, 1)
        self.txt_notas.foreground_color = colores["TEXTO"]
        form.add_widget(self.txt_notas)

        btn_reg = boton(ico("check") + t("register_btn", lang), CIAN, factor_escala=fs, height=dp(50))
        btn_reg.bind(on_release=lambda *_: self.registrar())
        form.add_widget(btn_reg)

        btn_pasada = boton(ico("calendario") + t("past_reading", lang), VIOLETA, factor_escala=fs, font_size=sp(12) * fs)
        btn_pasada.bind(on_release=lambda *_: self._popup_lectura_pasada())
        form.add_widget(btn_pasada)

        btn_recordatorios = boton(ico("campana") + t("reminders_btn", lang), AZUL, factor_escala=fs, font_size=sp(12) * fs)
        btn_recordatorios.bind(on_release=lambda *_: self._popup_recordatorios())
        form.add_widget(btn_recordatorios)
        cont.add_widget(form)

        # ================= PESTAÑA IMC =================
        cont = nueva_pestana("imc")
        card_cuerpo = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(10), spacing=dp(4),
                              size_hint_y=None, height=dp(150))
        card_cuerpo.add_widget(lbl(ico("peso") + t("body_title", lang), font_size=sp(14) * fs,
                                   color=colores["TEXTO_SUAVE"], shorten=True,
                                   size_hint_y=None, height=dp(22)))
        self.lb_cuerpo = lbl("—", font_size=sp(18) * fs, color=colores["TEXTO"], shorten=True)
        self.lb_cuerpo_sub = lbl("", font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"], shorten=True,
                                 size_hint_y=None, height=dp(22))
        card_cuerpo.add_widget(self.lb_cuerpo)
        card_cuerpo.add_widget(self.lb_cuerpo_sub)
        fila_btn_peso = BoxLayout(size_hint_y=None, height=dp(36), spacing=dp(6))
        btn_peso = boton(ico("mas") + t("register_weight", lang), VIOLETA, factor_escala=fs,
                         height=dp(36), font_size=sp(12) * fs)
        btn_peso.bind(on_release=lambda *_: self._popup_cuerpo())
        btn_peso_pasado = boton(ico("calendario") + t("past_weight_btn", lang), AZUL, factor_escala=fs,
                                height=dp(36), font_size=sp(12) * fs)
        btn_peso_pasado.bind(on_release=lambda *_: self._popup_peso_pasado())
        fila_btn_peso.add_widget(btn_peso)
        fila_btn_peso.add_widget(btn_peso_pasado)
        card_cuerpo.add_widget(fila_btn_peso)
        cont.add_widget(card_cuerpo)

        self.card_ref = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(10), spacing=dp(2),
                                size_hint_y=None, height=dp(160))
        cont.add_widget(self.card_ref)

        # ================= PESTAÑA ESTADÍSTICAS =================
        cont = nueva_pestana("stats")
        card_prom = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(10), spacing=dp(4),
                            size_hint_y=None, height=dp(82))
        h_prom = BoxLayout(size_hint_y=None, height=dp(28), spacing=dp(6))
        h_prom.add_widget(lbl(ico("promedio") + t("avg", lang), font_size=sp(14) * fs,
                              color=colores["TEXTO_SUAVE"], shorten=True))

        opciones_periodo = [t(k, lang) for k in ("filter_all", "filter_1w", "filter_2w",
                                                  "filter_1m", "filter_2m", "filter_3m")]
        idx = min(max(self._idx_periodo, 0), len(opciones_periodo) - 1)
        self.spn_periodo = selector(opciones_periodo[idx], opciones_periodo, factor_escala=fs,
                                    size_hint_x=0.55, height=dp(28), font_size=sp(12) * fs)
        self.spn_periodo.bind(text=self._on_cambio_periodo_unificado)
        h_prom.add_widget(self.spn_periodo)
        card_prom.add_widget(h_prom)

        fila_prom = BoxLayout(spacing=dp(6))
        self.lb_prom = lbl("—", font_size=sp(18) * fs, color=colores["TEXTO"], shorten=True,
                           size_hint_x=0.56)
        self.lb_prom_n = lbl("", font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"], shorten=True,
                             size_hint_x=0.44)
        fila_prom.add_widget(self.lb_prom)
        fila_prom.add_widget(self.lb_prom_n)
        card_prom.add_widget(fila_prom)
        cont.add_widget(card_prom)

        trend_header = BoxLayout(size_hint_y=None, height=dp(32), spacing=dp(8))
        trend_header.add_widget(lbl(ico("tendencia") + texto_degradado(t("trend", lang)),
                                    font_size=sp(12) * fs, shorten=True, size_hint_x=0.5))
        opc_modo = [t("chart_gluc", lang), t("chart_bmi", lang)]
        self.spn_modo = selector(opc_modo[min(self._idx_modo, 1)], opc_modo, factor_escala=fs,
                                 size_hint_x=0.5, height=dp(32), font_size=sp(12) * fs)
        self.spn_modo.bind(text=self._on_cambio_modo)
        trend_header.add_widget(self.spn_modo)
        cont.add_widget(trend_header)

        self.grafica = GraficaTendencia(self.app, size_hint_y=None, height=dp(180))
        cont.add_widget(self.grafica)

        card_st = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(10), spacing=dp(2),
                          size_hint_y=None, height=dp(206))
        card_st.add_widget(lbl(ico("grafica") + t("stats_title", lang), font_size=sp(14) * fs,
                               color=colores["TEXTO_SUAVE"], shorten=True,
                               size_hint_y=None, height=dp(24)))

        def fila_stat(clave):
            f = BoxLayout(size_hint_y=None, height=dp(30), spacing=dp(6))
            f.add_widget(lbl(t(clave, lang), font_size=sp(14) * fs, color=colores["TEXTO_SUAVE"],
                             shorten=True, size_hint_x=0.55))
            v = lbl("—", font_size=sp(15) * fs, color=colores["TEXTO"], halign="right",
                    shorten=True, size_hint_x=0.45, bold=True)
            f.add_widget(v)
            card_st.add_widget(f)
            return v

        self.st_min = fila_stat("stat_min")
        self.st_max = fila_stat("stat_max")
        self.st_rango = fila_stat("stat_inrange")
        self.st_fuera = fila_stat("stat_out")
        self.st_peso = fila_stat("stat_wchange")
        cont.add_widget(card_st)

        self.card_mom = Tarjeta(colores["CARD"], orientation="vertical", padding=dp(10), spacing=dp(2),
                                size_hint_y=None, height=dp(160))
        cont.add_widget(self.card_mom)

        # ================= PESTAÑA HISTORIAL =================
        cont = nueva_pestana("hist")
        exp = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        b_csv = boton(ico("csv") + t("export_csv", lang), AZUL, factor_escala=fs)
        b_txt = boton(ico("txt") + t("export_txt", lang), AZUL, factor_escala=fs)
        b_csv.bind(on_release=lambda *_: self.exportar("csv"))
        b_txt.bind(on_release=lambda *_: self.exportar("txt"))
        exp.add_widget(b_csv)
        exp.add_widget(b_txt)
        cont.add_widget(exp)

        fila_resp = BoxLayout(size_hint_y=None, height=dp(52) * ka, spacing=dp(8))
        b_resp = boton(ico("respaldo") + t("export_backup", lang), VIOLETA, factor_escala=fs,
                       height=dp(52) * ka, font_size=sp(13) * fs)
        b_imp = boton(ico("importar") + t("import_btn", lang), NARANJA, factor_escala=fs,
                      height=dp(52) * ka, font_size=sp(13) * fs)
        b_resp.bind(on_release=lambda *_: self.exportar_respaldo())
        b_imp.bind(on_release=lambda *_: self._popup_importar())
        fila_resp.add_widget(b_resp)
        fila_resp.add_widget(b_imp)
        cont.add_widget(fila_resp)

        b_wa = boton(ico("whatsapp") + t("share_wa", lang), VERDE_WA, factor_escala=fs)
        b_wa.bind(on_release=lambda *_: self.compartir_whatsapp())
        cont.add_widget(b_wa)

        h_hist = BoxLayout(size_hint_y=None, height=dp(34), spacing=dp(8))
        h_hist.add_widget(lbl(ico("reloj") + texto_degradado(t("history", lang)), font_size=sp(13) * fs,
                              shorten=True, size_hint_x=0.55))
        opc_hist = [t("tab_gluc", lang), t("hist_weight", lang)]
        self.spn_hist = selector(opc_hist[min(self._idx_hist, 1)], opc_hist, factor_escala=fs,
                                 size_hint_x=0.45, height=dp(34), font_size=sp(12) * fs)
        self.spn_hist.bind(text=self._on_cambio_hist)
        h_hist.add_widget(self.spn_hist)
        cont.add_widget(h_hist)

        self.lista = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
        self.lista.bind(minimum_height=self.lista.setter("height"))
        cont.add_widget(self.lista)

        # ---------------- ENSAMBLE: celular 1 columna / tableta 2 columnas ----------------
        def barra_tabs(claves, pesos=None):
            bar = BoxLayout(size_hint_y=None, height=dp(46) * ka, spacing=dp(4))
            for c in claves:
                self._botones_tab[c].size_hint_x = (pesos or {}).get(c, 1)
                bar.add_widget(self._botones_tab[c])
            return bar

        self.add_widget(top_bar)
        if not self._ancho:
            self.add_widget(self.logo_contenedor)
            self.add_widget(barra)
            self.add_widget(barra_tabs(("gluc", "imc", "stats", "hist"),
                                       {"gluc": 0.25, "imc": 0.17, "stats": 0.33, "hist": 0.25}))
            self.contenido = BoxLayout()
            self.add_widget(self.contenido)
            self._mostrar_tab(self._tab_actual)
        else:
            columnas = BoxLayout(orientation="horizontal", spacing=dp(12))
            izq = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_x=0.42)
            der = BoxLayout(orientation="vertical", spacing=dp(8), size_hint_x=0.58)
            izq.add_widget(self.logo_contenedor)
            izq.add_widget(barra)
            izq.add_widget(barra_tabs(("gluc", "imc")))
            self.cont_izq = BoxLayout()
            izq.add_widget(self.cont_izq)
            der.add_widget(barra_tabs(("stats", "hist")))
            self.cont_der = BoxLayout()
            der.add_widget(self.cont_der)
            columnas.add_widget(izq)
            columnas.add_widget(der)
            self.add_widget(columnas)
            self._mostrar_tab(self._tab_izq)
            self._mostrar_tab(self._tab_der)
        self._actualizar_reloj()

    def _actualizar_reloj(self, *_):
        ahora = datetime.now()
        fmt = "%H:%M" if self.app.formato_24h else "%I:%M %p"
        self.btn_reloj.text = ico("reloj") + ahora.strftime(fmt)

    def _alternar_formato_reloj(self, *_):
        self.app.formato_24h = not self.app.formato_24h
        self.app.guardar_preferencias()
        self._actualizar_reloj()

    def _alternar_tema_directo(self, *_):
        self.app.tema_actual = "light" if self.app.tema_actual == "dark" else "dark"
        self.app.guardar_preferencias()
        self.actualizar_estilos()

    def _alternar_lang_directo(self, *_):
        self.app.idioma_actual = "en" if self.app.idioma_actual == "es" else "es"
        self.app.guardar_preferencias()
        self.actualizar_estilos()

    def refrescar(self, *_):
        perfil = self.gestor.activo
        colores = TEMAS[self.app.tema_actual]
        fs = self.app.factor_escala_global
        lang = self.app.idioma_actual

        self._actualizando = True
        self.spn_perfil.values = self.gestor.nombres()
        self.spn_perfil.text = perfil.nombre
        self._actualizando = False

        # semáforo de tiras: <=15 amarillo, <=10 rojo
        if hasattr(self.app, "lb_tiras_logo"):
            self.app.lb_tiras_logo.text = "[b]%d[/b]" % perfil.tiras
            nivel = perfil.nivel_tiras
            if nivel == "rojo":
                self.app.card_tiras_logo.set_color(colores["ROJO_OSCURO"])
                self.app.lb_tiras_logo.color = col_t(ROJO, colores["ROJO_OSCURO"])
            elif nivel == "amarillo":
                self.app.card_tiras_logo.set_color(colores["AMARILLO_OSCURO"])
                self.app.lb_tiras_logo.color = col_t(colores["AMARILLO"], colores["AMARILLO_OSCURO"])
            else:
                self.app.card_tiras_logo.set_color(colores["CARD"])
                self.app.lb_tiras_logo.color = colores["TEXTO"]

        self.actualizar_todo_por_periodo(perfil)
        self.actualizar_cuerpo(perfil)

        self._poblar_historial(perfil)

    def _dias_desde_filtro(self, texto):
        try:
            return DIAS_FILTRO[list(self.spn_periodo.values).index(texto)]
        except (ValueError, IndexError):
            return None

    def actualizar_todo_por_periodo(self, perfil):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        dias = self._dias_desde_filtro(self.spn_periodo.text)

        filtradas = perfil.lecturas_filtradas(dias)
        n = len(filtradas)
        prom = perfil.promedio_filtrado(dias)

        if prom is None:
            self.lb_prom.color = colores["TEXTO"]
            self.lb_prom.text = "[b]—[/b]"
            self.lb_prom_n.text = ""
            self.app.lb_prom_logo.text = "—"
            self.app.lb_prom_logo.color = colores["TEXTO_SUAVE"]
        else:
            col = COLOR_ESTADO[estado_valor(prom)]
            etiqueta = t("reading_one", lang) if n == 1 else t("readings_count", lang)
            self.lb_prom.color = col_t(col)
            self.lb_prom.text = "[b]%.0f mg/dL[/b]" % prom
            self.lb_prom_n.text = "· %d %s" % (n, etiqueta)
            # promedio junto a las tiras: solo el número
            self.app.lb_prom_logo.text = ico("promedio") + "%.0f" % prom
            self.app.lb_prom_logo.color = col_t(col, self.app.card_tiras_logo._color.rgba)

        self._poblar_momentos(filtradas)
        vals = [r["valor"] for r in filtradas]
        if vals:
            altas = sum(1 for v in vals if v > RANGO_MAX)
            bajas = sum(1 for v in vals if v < RANGO_MIN)
            self.st_min.text = "%g mg/dL" % min(vals)
            self.st_min.color = col_t(COLOR_ESTADO[estado_valor(min(vals))])
            self.st_max.text = "%g mg/dL" % max(vals)
            self.st_max.color = col_t(COLOR_ESTADO[estado_valor(max(vals))])
            self.st_rango.text = "%.0f %%" % (100.0 * (len(vals) - altas - bajas) / len(vals))
            self.st_fuera.text = "%d / %d" % (altas, bajas)
        else:
            for w in (self.st_min, self.st_max, self.st_rango, self.st_fuera):
                w.text = "—"
            self.st_min.color = self.st_max.color = colores["TEXTO"]
        meds = perfil.medidas_con_imc(dias)
        self.st_peso.text = ("%+.1f kg" % (meds[-1][1] - meds[0][1])) if len(meds) >= 2 else "—"

        if dias is None:
            filtradas = filtradas[-100:]
        self.grafica.modo = MODOS_GRAFICA[min(self._idx_modo, 1)]
        self.grafica.datos = [r["valor"] for r in filtradas]
        meds_g = [m for m in perfil.medidas_con_imc(dias) if m[2] is not None]
        self.grafica.refs_imc = perfil.refs_para([m[0] for m in meds_g]) if meds_g else []
        self.grafica.puntos_i = [(_ts_num(m[0]), m[2], perfil.categoria_en(m[2], m[0])) for m in meds_g]

    def _color_imc(self, cat, texto=False):
        col = color_cat(cat)
        return col_t(col) if texto else col

    def _poblar_ref(self, perfil):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        card = self.card_ref
        card.clear_widgets()
        meses = perfil.edad_meses()
        menor = meses is not None and 0 <= meses < EDAD_ADULTO_MESES
        nota = None
        if not menor:
            titulo = t("bmi_ref", lang)
            filas = [("low", "< 18.5"), ("normal", "18.5 – 24.9"), ("over", "25 – 29.9"), ("obese", "30+")]
        else:
            ap = perfil.edad_partes()
            titulo = "%s · %s" % (t("bmi_ref_child", lang), t("age_fmt", lang) % ap)
            c = cortes_oms(perfil.sexo, meses)
            if c is None:
                filas, nota = [], t("bmi_ref_na", lang)
            else:
                filas = [("severe", "< %.1f" % c[0]), ("low", "%.1f – %.1f" % (c[0], c[1])),
                         ("normal", "%.1f – %.1f" % (c[1], c[4])), ("over", "%.1f – %.1f" % (c[4], c[5])),
                         ("obese", "> %.1f" % c[5])]
                nota = t("bmi_ref_note", lang)
        card.add_widget(lbl(ico("peso") + titulo, font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"],
                            shorten=True, size_hint_y=None, height=dp(24)))
        for cat, rango in filas:
            card.add_widget(lbl("[color=%s][b]%s[/b]   %s[/color]" % (
                hexa(self._color_imc(cat, texto=True)), rango, t("bmi_" + cat, lang)),
                font_size=sp(14) * fs, shorten=True, size_hint_y=None, height=dp(28)))
        if nota:
            card.add_widget(lbl(nota, font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"],
                                size_hint_y=None, height=dp(76), ajuste="multi", valign="top"))
        card.height = dp(24 + 26 * len(filas) + (76 if nota else 0) + 28)

    def actualizar_cuerpo(self, perfil):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        self._poblar_ref(perfil)
        btn = getattr(self.app, "btn_imc_logo", None)
        if btn is not None:
            if perfil.tiene_datos_cuerpo:
                col_b = self._color_imc(perfil.categoria_en(perfil.imc_actual, perfil.medidas[-1]["ts"]))
                btn.text = "%s %.1f" % (t("bmi", lang), perfil.imc_actual)
            else:
                col_b = VIOLETA
                btn.text = ico("mas") + t("bmi", lang)
            btn.background_color = col_b
            btn.color = texto_sobre(col_b)
        if perfil.tiene_datos_cuerpo:
            imc = perfil.imc_actual
            cat = perfil.categoria_en(imc, perfil.medidas[-1]["ts"])
            self.lb_cuerpo.color = self._color_imc(cat, texto=True)
            self.lb_cuerpo.text = "[b]%.1f kg[/b]  ·  %s %.1f" % (perfil.peso_actual, t("bmi", lang), imc)
            self.lb_cuerpo_sub.text = "%s · %g cm · %s" % (
                t("sex_m" if perfil.sexo == "M" else "sex_f", lang), perfil.estatura, t("bmi_" + cat, lang))
        else:
            self.lb_cuerpo.color = colores["TEXTO"]
            self.lb_cuerpo.text = "—"
            self.lb_cuerpo_sub.text = t("body_needed", lang)

    def _fila_peso(self, ts, peso, imc):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        cat = self.gestor.activo.categoria_en(imc, ts) if imc is not None else None
        col = self._color_imc(cat, texto=True) if cat else colores["TEXTO"]
        try:
            fecha = datetime.fromisoformat(ts).strftime("%d/%m/%y")
        except ValueError:
            fecha = str(ts)
        fila = Tarjeta(colores["CARD"], orientation="horizontal", size_hint_y=None,
                       height=dp(54) * k_alto(), padding=dp(10), spacing=dp(8))
        fila.add_widget(lbl("[b]%.1f kg[/b]" % peso, color=col, font_size=sp(16) * fs,
                            shorten=True, size_hint_x=0.28))
        fila.add_widget(lbl(("%s %.1f · %s" % (t("bmi", lang), imc, t("bmi_" + cat, lang))) if cat else "",
                            color=col, font_size=sp(14) * fs, shorten=True, size_hint_x=0.42))
        fila.add_widget(lbl(fecha, color=colores["TEXTO_SUAVE"], font_size=sp(14) * fs,
                            halign="right", shorten=True, size_hint_x=0.30))
        return fila

    def _mostrar_tab(self, clave):
        if clave not in self._tabs:
            clave = "gluc"
        self._tab_actual = clave
        if self._ancho:
            if clave in ("gluc", "imc"):
                self._tab_izq = clave
                destino = self.cont_izq
            else:
                self._tab_der = clave
                destino = self.cont_der
            destino.clear_widgets()
            destino.add_widget(self._tabs[clave])
            activas = (self._tab_izq, self._tab_der)
        else:
            self.contenido.clear_widgets()
            self.contenido.add_widget(self._tabs[clave])
            activas = (clave,)
        for c, b in self._botones_tab.items():
            col = CIAN if c in activas else (0.2, 0.3, 0.4, 1)
            b.background_color = col
            b.color = texto_sobre(col)

    def _poblar_historial(self, perfil):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        self.lista.clear_widgets()
        if self._idx_hist == 0:
            filas = [self._fila_historial(r) for r in reversed(perfil.ultimas(50))]
            vacio = t("no_readings", lang)
        else:
            filas = [self._fila_peso(ts, pes, imc)
                     for ts, pes, imc in list(reversed(perfil.medidas_con_imc()))[:50]]
            vacio = t("no_weights", lang)
        if not filas:
            self.lista.add_widget(lbl(vacio, color=colores["TEXTO_SUAVE"], size_hint_y=None,
                                      height=dp(36), font_size=sp(12) * fs, shorten=True))
        for f in filas:
            self.lista.add_widget(f)

    # ---------------- pantalla ancha ----------------
    def _es_ancho(self):
        return Window.width >= dp(ANCHO_TABLETA_DP)

    def _on_ventana(self, *_):
        Clock.unschedule(self._reevaluar_ancho)
        Clock.schedule_once(self._reevaluar_ancho, 0.4)

    def _reevaluar_ancho(self, *_):
        if self._es_ancho() != self._ancho:
            self.actualizar_estilos()

    # ---------------- promedios por momento del día ----------------
    def _poblar_momentos(self, lecturas):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        card = self.card_mom
        card.clear_widgets()
        nombres = MOMENTOS_ES if lang == "es" else MOMENTOS_EN
        pm = promedios_por_momento(lecturas)
        card.add_widget(lbl(ico("reloj") + t("by_moment", lang), font_size=sp(14) * fs,
                            color=colores["TEXTO_SUAVE"], shorten=True, size_hint_y=None, height=dp(24)))
        filas = [i for i in range(len(nombres)) if i in pm or i < 3]   # los 3 principales siempre
        for i in filas:
            f = BoxLayout(size_hint_y=None, height=dp(30), spacing=dp(6))
            f.add_widget(lbl(nombres[i], font_size=sp(14) * fs, color=colores["TEXTO_SUAVE"],
                             shorten=True, size_hint_x=0.5))
            if i in pm:
                txt = "%.0f mg/dL · %d" % pm[i]
                col = col_t(COLOR_ESTADO[estado_valor(pm[i][0])])
            else:
                txt, col = "—", colores["TEXTO"]
            f.add_widget(lbl(txt, font_size=sp(15) * fs, color=col, halign="right", bold=True,
                             shorten=True, size_hint_x=0.5))
            card.add_widget(f)
        card.height = dp(20 + 24 + 32 * len(filas))

    # ---------------- compartir por WhatsApp ----------------
    @blindado
    def compartir_whatsapp(self):
        perfil = self.gestor.activo
        lang = self.app.idioma_actual
        dias = self._dias_desde_filtro(self.spn_periodo.text)
        texto = resumen_compartir(perfil, lang, dias, self.spn_periodo.text)
        if not texto:
            raise ErrorUsuario(t("no_readings", lang))
        try:
            abierto = webbrowser.open("https://api.whatsapp.com/send?text=" + quote(texto))
        except Exception:
            abierto = False
        if not abierto:
            try:
                from kivy.core.clipboard import Clipboard
                Clipboard.copy(texto)
                mostrar_aviso(t("share_wa", lang), t("wa_copied", lang))
            except Exception:
                mostrar_aviso(t("share_wa", lang), t("wa_fail", lang))

    # ---------------- recordatorios: notificación a la hora indicada ----------------
    def _revisar_recordatorios(self, *_):
        ahora = datetime.now()
        marca = ahora.strftime("%Y%m%d%H%M")
        for perfil in self.gestor.perfiles.values():
            for rem in perfil.recordatorios:
                if not rem.get("activo"):
                    continue
                try:
                    h = datetime.strptime(str(rem["hora"]).strip(), "%I:%M %p")
                except ValueError:
                    continue
                if h.hour == ahora.hour and h.minute == ahora.minute:
                    clave = (perfil.id, rem["titulo"], rem["hora"], marca)
                    if clave in self._avisados:
                        continue
                    self._avisados.add(clave)
                    self._lanzar_aviso(perfil, rem)
        if len(self._avisados) > 300:
            self._avisados = {c for c in self._avisados if c[3] == marca}

    def _lanzar_aviso(self, perfil, rem):
        lang = self.app.idioma_actual
        titulo = t("rem_title", lang)
        mensaje = "%s: %s (%s)" % (perfil.nombre, rem["titulo"], rem["hora"])
        if not enviar_notificacion(titulo, mensaje):
            mostrar_aviso(titulo, mensaje)      # respaldo visual dentro de la app

    # ---------------- respaldo e importación ----------------
    @blindado
    def exportar_respaldo(self):
        ruta = self.gestor.exportar_respaldo(self.app.user_data_dir)
        lang = self.app.idioma_actual
        mostrar_aviso(t("export_ready", lang), t("file_saved", lang) % ruta)

    def _popup_importar(self):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        caja.add_widget(lbl(t("import_hint", lang), font_size=sp(12) * fs, color=colores["TEXTO_SUAVE"],
                            size_hint_y=None, height=dp(50), valign="top", ajuste="multi"))
        inicio = next((c for c in GestorGlucosa._candidatos_exportacion(self.app.user_data_dir)
                       if c and os.path.isdir(c)), os.path.expanduser("~"))
        marco = Tarjeta((0.13, 0.15, 0.20, 1), padding=dp(4))   # fondo oscuro fijo: el selector usa letra clara
        try:
            chooser = FileChooserListView(path=inicio, filters=["*.json", "*.csv"], dirselect=False)
        except Exception:
            chooser = None
        if chooser is not None:
            marco.add_widget(chooser)
        caja.add_widget(marco)
        ent_ruta = campo(hint_text=t("import_path_hint", lang), font_size=sp(12) * fs, height=dp(44))
        caja.add_widget(ent_ruta)
        botones = BoxLayout(size_hint_y=None, height=dp(48) * k_alto(), spacing=dp(8))
        b_cancel = boton(ico("cerrar") + t("cancel", lang), GRIS, factor_escala=fs)
        b_ok = boton(ico("importar") + t("import_load", lang), NARANJA, factor_escala=fs)
        botones.add_widget(b_cancel)
        botones.add_widget(b_ok)
        caja.add_widget(botones)
        pop = popup_tema(title=t("import_title", lang), content=caja, size_hint=(0.95, 0.92),
                         separator_color=NARANJA)

        if chooser is not None:
            def al_elegir(_inst, sel):
                if sel:
                    ent_ruta.text = sel[0]
            chooser.bind(selection=al_elegir)

        @blindado
        def cargar(*_):
            tipo, datos, activo = self.gestor.leer_respaldo(ent_ruta.text.strip())
            pop.dismiss()
            self._confirmar_importacion(tipo, datos, activo)

        b_ok.bind(on_release=cargar)
        b_cancel.bind(on_release=pop.dismiss)
        pop.open()

    def _confirmar_importacion(self, tipo, datos, activo):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        if tipo == "json":
            resumen = t("import_json_sum", lang) % (
                len(datos), sum(len(p.lecturas) for p in datos), sum(len(p.medidas) for p in datos))
        else:
            resumen = t("import_csv_sum", lang) % (len(datos.lecturas), len(datos.medidas),
                                                     escape_markup(self.gestor.activo.nombre))
        caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        txt = "[b]%s[/b]\n\n%s" % (t("import_found", lang), resumen)
        if tipo == "json":
            txt += "\n\n" + t("import_replace_warn", lang)
        caja.add_widget(lbl(txt, font_size=sp(13) * fs, color=colores["TEXTO"], valign="top", ajuste="multi"))
        fila = BoxLayout(size_hint_y=None, height=dp(48) * k_alto(), spacing=dp(6))
        b_no = boton(t("cancel", lang), GRIS, factor_escala=fs)
        b_fus = boton(t("import_merge", lang), CIAN, factor_escala=fs)
        b_rep = boton(t("import_replace", lang), ROJO, factor_escala=fs)
        fila.add_widget(b_no)
        fila.add_widget(b_fus)
        if tipo == "json":
            fila.add_widget(b_rep)
        caja.add_widget(fila)
        pop = popup_tema(title=t("import_title", lang), content=caja, size_hint=(0.92, 0.6),
                         separator_color=NARANJA)

        def ejecutar(modo):
            @blindado
            def _go(*_):
                res = self.gestor.importar(tipo, datos, modo, activo_id=activo)
                pop.dismiss()
                self.refrescar()
                mostrar_aviso(t("import_done", lang), t("import_done_txt", lang) % (
                    res["perfiles"], res["lecturas"], res["pesos"], res["recordatorios"]))
            return _go

        b_fus.bind(on_release=ejecutar("fusionar"))
        b_rep.bind(on_release=ejecutar("reemplazar"))
        b_no.bind(on_release=pop.dismiss)
        pop.open()

    @blindado
    def _on_cambio_hist(self, spinner, texto):
        try:
            self._idx_hist = list(spinner.values).index(texto)
        except ValueError:
            self._idx_hist = 0
        self._poblar_historial(self.gestor.activo)

    @blindado
    def _on_cambio_modo(self, spinner, texto):
        try:
            self._idx_modo = list(spinner.values).index(texto)
        except ValueError:
            self._idx_modo = 0
        self.actualizar_todo_por_periodo(self.gestor.activo)

    def _arranque(self, *_):
        if not self.app.aviso_aceptado:
            self._popup_aviso(inicial=True)
        else:
            self._pedir_datos_cuerpo()

    def _popup_aviso(self, inicial=False):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        sv = ScrollView(do_scroll_x=False, bar_width=dp(3))
        sv.add_widget(_texto_largo(t("disc_text", lang), fs, colores["TEXTO"]))
        caja.add_widget(sv)
        fila = BoxLayout(size_hint_y=None, height=dp(48), spacing=dp(8))
        b_ayuda = boton(ico("info") + t("help_title", lang), AZUL, factor_escala=fs)
        b_ok = boton(ico("check") + t("disc_accept", lang) if inicial else ico("cerrar") + t("close", lang),
                     VERDE if inicial else CIAN, factor_escala=fs)
        if inicial:
            fila.add_widget(b_ayuda)
        fila.add_widget(b_ok)
        caja.add_widget(fila)
        pop = popup_tema(title=t("disc_title", lang), content=caja, size_hint=(0.94, 0.82),
                         auto_dismiss=not inicial, separator_color=ROJO)

        def aceptar(*_):
            if inicial:
                self.app.aviso_aceptado = True
                self.app.guardar_preferencias()
            pop.dismiss()
            if inicial:
                Clock.schedule_once(self._pedir_datos_cuerpo, 0.3)

        b_ok.bind(on_release=aceptar)
        b_ayuda.bind(on_release=lambda *_: abrir_ayuda(self.app))
        pop.open()

    def _pedir_datos_cuerpo(self, *_):
        perfil = self.gestor.activo
        if not perfil.tiene_datos_cuerpo:
            self._popup_cuerpo(perfil)

    def _popup_cuerpo(self, perfil=None):
        perfil = perfil or self.gestor.activo
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        caja.add_widget(lbl(ico("usuario") + "[b]%s[/b]" % escape_markup(perfil.nombre),
                            font_size=sp(14) * fs, color=colores["TEXTO_SUAVE"],
                            size_hint_y=None, height=dp(26), shorten=True))
        caja.add_widget(lbl(t("body_update_prompt" if perfil.tiene_datos_cuerpo else "body_prompt", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(34), ajuste="multi"))

        sexos = [t("sex_m", lang), t("sex_f", lang)]
        ini = sexos[0] if perfil.sexo == "M" else (sexos[1] if perfil.sexo == "F" else t("sex", lang))
        spn_sexo = selector(ini, sexos, factor_escala=fs, height=dp(46))
        caja.add_widget(spn_sexo)

        fila_edad = BoxLayout(size_hint_y=None, height=dp(50), spacing=dp(8))
        ap = perfil.edad_partes()
        ent_anios = campo(hint_text=t("age_years", lang), input_filter="int", input_type="number",
                          text=str(ap[0]) if ap else "", font_size=sp(15) * fs,
                          height=dp(50), size_hint_x=0.5)
        ent_meses = campo(hint_text=t("age_months", lang), input_filter="int", input_type="number",
                          text=str(ap[1]) if ap else "", font_size=sp(15) * fs,
                          height=dp(50), size_hint_x=0.5)
        fila_edad.add_widget(ent_anios)
        fila_edad.add_widget(ent_meses)
        caja.add_widget(fila_edad)

        fila = BoxLayout(size_hint_y=None, height=dp(50), spacing=dp(8))
        ent_est = campo(hint_text=t("height_cm", lang), input_filter="float", input_type="number",
                        text=("%g" % perfil.estatura) if perfil.estatura else "",
                        font_size=sp(15) * fs, height=dp(50), size_hint_x=0.5)
        ent_peso = campo(hint_text=t("weight_kg", lang), input_filter="float", input_type="number",
                         font_size=sp(15) * fs, height=dp(50), size_hint_x=0.5)
        fila.add_widget(ent_est)
        fila.add_widget(ent_peso)
        caja.add_widget(fila)
        caja.add_widget(Widget())

        botones = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        b_later = boton(t("later", lang), GRIS, factor_escala=fs)
        b_ok = boton(ico("check") + t("save", lang), CIAN, factor_escala=fs)
        botones.add_widget(b_later)
        botones.add_widget(b_ok)
        caja.add_widget(botones)
        pop = popup_tema(title=t("body_title", lang), content=caja, size_hint=(0.92, 0.74),
                    separator_color=VIOLETA)

        @blindado
        def guardar(*_):
            sexo = "M" if spn_sexo.text == sexos[0] else ("F" if spn_sexo.text == sexos[1] else "")
            a_txt, m_txt = ent_anios.text, ent_meses.text
            if perfil.nacimiento and a_txt.strip().isdigit() and \
                    (int(a_txt), int(m_txt or 0)) == perfil.edad_partes():
                a_txt = m_txt = None      # edad sin cambios: se conserva la fecha calculada
            perfil.registrar_cuerpo(sexo, ent_est.text, ent_peso.text, a_txt, m_txt)
            self.gestor.guardar()
            pop.dismiss()
            self.refrescar()

        b_ok.bind(on_release=guardar)
        b_later.bind(on_release=pop.dismiss)
        pop.open()

    @blindado
    def _on_cambio_periodo_unificado(self, spinner, texto):
        if self._actualizando:
            return
        try:
            self._idx_periodo = list(spinner.values).index(texto)
        except ValueError:
            self._idx_periodo = 0
        self.actualizar_todo_por_periodo(self.gestor.activo)

    @blindado
    def _on_cambio_perfil(self, spinner, nombre):
        if self._actualizando or not nombre:
            return
        self.gestor.cambiar_por_nombre(nombre)
        self.refrescar()
        Clock.schedule_once(self._pedir_datos_cuerpo, 0.3)

    def _fila_historial(self, r):
        colores = TEMAS[self.app.tema_actual]
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        est = estado_valor(r["valor"])
        col = col_t(COLOR_ESTADO[est])
        fila = Tarjeta(colores["CARD"], orientation="horizontal", size_hint_y=None,
                       height=dp(68) * k_alto(), padding=dp(10), spacing=dp(8))

        izq = BoxLayout(orientation="vertical", size_hint_x=0.32)
        izq.add_widget(lbl("[b]%s[/b]" % r["valor"], color=col, font_size=sp(19) * fs,
                           shorten=True, size_hint_y=0.58))
        izq.add_widget(lbl("mg/dL · %s" % t("st_" + est, lang), color=col,
                           font_size=sp(14) * fs, shorten=True, size_hint_y=0.42))
        fila.add_widget(izq)

        try:
            fecha = datetime.fromisoformat(r["ts"]).strftime("%d/%m/%y %I:%M %p")
        except ValueError:
            fecha = str(r["ts"])
        der = BoxLayout(orientation="vertical", size_hint_x=0.68)
        der.add_widget(lbl("%s%s  ·  %s" % (ico("reloj"), fecha, escape_markup(str(r["momento"]))),
                           font_size=sp(14) * fs, color=colores["TEXTO"], shorten=True))
        if r["notas"]:
            der.add_widget(lbl("[color=%s]%s%s[/color]" % (hexa(colores["TEXTO_SUAVE"]), ico("nota"),
                                                           escape_markup(str(r["notas"]))),
                               font_size=sp(13) * fs, shorten=True))
        fila.add_widget(der)
        return fila

    @blindado
    def registrar(self):
        perfil = self.gestor.activo
        perfil.registrar(self.txt_valor.text, self.spn_momento.text,
                         self.txt_notas.text)
        self.gestor.guardar()
        self.txt_valor.text = ""
        self.txt_notas.text = ""
        self.txt_valor.focus = False
        self.txt_notas.focus = False
        self.refrescar()
        if perfil.tiras == 0:
            mostrar_aviso("Sin tiras", "Se agotó el inventario de tiras reactivas.")

    @blindado
    def exportar(self, formato):
        perfil = self.gestor.activo
        if not perfil.lecturas:
            raise ErrorUsuario("No hay lecturas para exportar.")
        respaldo = self.app.user_data_dir
        if formato == "csv":
            ruta = self.gestor.exportar_csv(perfil, respaldo)
        else:
            ruta = self.gestor.exportar_txt(perfil, respaldo)
        lang = self.app.idioma_actual
        mostrar_aviso(t("export_ready", lang), t("file_saved", lang) % ruta)

    def _popup_recordatorios(self):
        lang = self.app.idioma_actual
        perfil = self.gestor.activo
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]

        caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(8))
        caja.add_widget(lbl(ico("campana") + texto_degradado(t("reminders_title", lang)),
                            font_size=sp(14) * fs, size_hint_y=None, height=dp(26), shorten=True))

        scroll_rem = ScrollView(do_scroll_x=False, bar_width=dp(3), size_hint_y=0.45)
        lista_rem = GridLayout(cols=1, spacing=dp(6), size_hint_y=None)
        lista_rem.bind(minimum_height=lista_rem.setter("height"))

        def confirmar_borrar(index):
            if not (0 <= index < len(perfil.recordatorios)):
                return
            titulo = perfil.recordatorios[index]["titulo"]
            c = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
            c.add_widget(lbl("[color=%s]%s[/color]" % (hexa(colores["TEXTO"]), t("delete_rem_q", lang) % escape_markup(titulo)),
                             halign="center", font_size=sp(13) * fs, ajuste="multi"))
            f2 = BoxLayout(size_hint_y=None, height=dp(44), spacing=dp(8))
            b_no = boton(t("cancel", lang), GRIS, factor_escala=fs, height=dp(44))
            b_si = boton(ico("basura") + t("delete", lang), ROJO, factor_escala=fs, height=dp(44))
            f2.add_widget(b_no)
            f2.add_widget(b_si)
            c.add_widget(f2)
            pop_c = popup_tema(title=t("delete", lang), content=c, size_hint=(0.85, 0.34),
                          separator_color=ROJO)

            @blindado
            def borrar(*_):
                if 0 <= index < len(perfil.recordatorios):
                    perfil.recordatorios.pop(index)
                    self.gestor.guardar()
                pop_c.dismiss()
                actualizar_lista_rem()

            b_si.bind(on_release=borrar)
            b_no.bind(on_release=pop_c.dismiss)
            pop_c.open()

        def actualizar_lista_rem():
            lista_rem.clear_widgets()
            for i, rem in enumerate(perfil.recordatorios):
                fila = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(6))
                lb_info = lbl("[b]%s[/b] — [color=%s]%s[/color]"
                              % (escape_markup(rem['titulo']),
                                 hexa(col_t(CIAN, colores["BG"])), escape_markup(rem['hora'])),
                              font_size=sp(12) * fs, color=colores["TEXTO"], shorten=True,
                              size_hint_x=0.50)
                btn_estado = boton("ON" if rem["activo"] else "OFF",
                                   VERDE if rem["activo"] else (0.4, 0.4, 0.4, 1),
                                   factor_escala=fs, size_hint_x=0.25, height=dp(42))
                btn_borrar = boton(ico("basura", espacio=False), ROJO, factor_escala=fs,
                                   size_hint_x=0.25, height=dp(42))

                @blindado
                def toggle_rem(btn_inst, index=i):
                    estado_actual = perfil.recordatorios[index]["activo"]
                    if not estado_actual:
                        r_ = perfil.recordatorios[index]
                        if not enviar_notificacion(t("rem_note_title", lang), "%s · %s" % (r_["titulo"], r_["hora"])):
                            mostrar_aviso(t("rem_note_title", lang), t("rem_note", lang))
                    perfil.recordatorios[index]["activo"] = not estado_actual
                    self.gestor.guardar()
                    actualizar_lista_rem()

                btn_estado.bind(on_release=toggle_rem)
                btn_borrar.bind(on_release=lambda _b, index=i: confirmar_borrar(index))
                fila.add_widget(lb_info)
                fila.add_widget(btn_estado)
                fila.add_widget(btn_borrar)
                lista_rem.add_widget(fila)

        actualizar_lista_rem()
        scroll_rem.add_widget(lista_rem)
        caja.add_widget(scroll_rem)

        caja.add_widget(lbl(ico("reloj") + t("rem_time", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(20), shorten=True))

        caja_nuevo = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        txt_titulo_rem = campo(hint_text=t("rem_name_hint", lang), size_hint_x=0.40,
                               font_size=sp(12) * fs, height=dp(42))

        horas_12_val = [f"{h:02d}" for h in range(1, 13)]
        minutos_val = [f"{m:02d}" for m in range(0, 60, 5)]
        ampm_val = ["AM", "PM"]

        spn_hr12 = selector("08", horas_12_val, factor_escala=fs, size_hint_x=0.22, height=dp(42))
        spn_min = selector("00", minutos_val, factor_escala=fs, size_hint_x=0.20, height=dp(42))
        spn_ampm = selector("AM", ampm_val, factor_escala=fs, size_hint_x=0.18, height=dp(42))

        caja_nuevo.add_widget(txt_titulo_rem)
        caja_nuevo.add_widget(spn_hr12)
        caja_nuevo.add_widget(spn_min)
        caja_nuevo.add_widget(spn_ampm)
        caja.add_widget(caja_nuevo)

        btn_agregar = boton(ico("mas") + t("add_reminder", lang), VIOLETA, factor_escala=fs, height=dp(42))

        @blindado
        def agregar_nuevo_rem(*_):
            tit = txt_titulo_rem.text.strip()
            if not tit:
                raise ErrorUsuario("Escribe un nombre para el recordatorio.")
            hora_str = f"{spn_hr12.text}:{spn_min.text} {spn_ampm.text}"
            perfil.recordatorios.append({"titulo": tit, "hora": hora_str, "activo": True})
            self.gestor.guardar()
            txt_titulo_rem.text = ""
            actualizar_lista_rem()

        btn_agregar.bind(on_release=agregar_nuevo_rem)
        caja.add_widget(btn_agregar)

        b_cerrar = boton(ico("cerrar") + t("close", lang), CIAN, factor_escala=fs, height=dp(42))
        caja.add_widget(b_cerrar)

        pop = popup_tema(title=t("reminders_btn", lang), content=caja, size_hint=(0.95, 0.82),
                    separator_color=VIOLETA)
        b_cerrar.bind(on_release=pop.dismiss)
        pop.open()

    def _bloque_fecha_hora(self, caja):
        # Calendario (día/mes/año) y reloj 12h (hora, minuto, AM/PM). Devuelve una
        # función que valida y entrega la fecha como texto ISO.
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        ahora = datetime.now()

        caja.add_widget(lbl(ico("calendario") + t("past_date", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(20), shorten=True))
        fila_fecha = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        dias_val = [f"{d:02d}" for d in range(1, 32)]
        meses_val = [f"{m:02d}" for m in range(1, 13)]
        anios_val = [str(y) for y in range(2020, 2031)]
        spn_dia = selector(f"{ahora.day:02d}", dias_val, factor_escala=fs, size_hint_x=0.30, height=dp(42))
        spn_mes = selector(f"{ahora.month:02d}", meses_val, factor_escala=fs, size_hint_x=0.35, height=dp(42))
        spn_anio = selector(str(ahora.year), anios_val, factor_escala=fs, size_hint_x=0.35, height=dp(42))
        fila_fecha.add_widget(spn_dia)
        fila_fecha.add_widget(spn_mes)
        fila_fecha.add_widget(spn_anio)
        caja.add_widget(fila_fecha)

        caja.add_widget(lbl(ico("reloj") + t("past_time", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(20), shorten=True))
        fila_hora = BoxLayout(size_hint_y=None, height=dp(42), spacing=dp(6))
        horas_12_val = [f"{h:02d}" for h in range(1, 13)]
        minutos_val = [f"{m:02d}" for m in range(0, 60, 5)]
        hr_actual_12 = ahora.hour % 12 or 12
        ampm_actual = "PM" if ahora.hour >= 12 else "AM"
        min_actual = (ahora.minute // 5) * 5  # el selector va de 5 en 5
        spn_hr12 = selector(f"{hr_actual_12:02d}", horas_12_val, factor_escala=fs, size_hint_x=0.36, height=dp(42))
        spn_min = selector(f"{min_actual:02d}", minutos_val, factor_escala=fs, size_hint_x=0.34, height=dp(42))
        spn_ampm = selector(ampm_actual, ["AM", "PM"], factor_escala=fs, size_hint_x=0.30, height=dp(42))
        fila_hora.add_widget(spn_hr12)
        fila_hora.add_widget(spn_min)
        fila_hora.add_widget(spn_ampm)
        caja.add_widget(fila_hora)

        def obtener_ts():
            try:
                hr12 = int(spn_hr12.text)
                ap = spn_ampm.text.upper()
                if ap == "PM" and hr12 < 12:
                    hr24 = hr12 + 12
                elif ap == "AM" and hr12 == 12:
                    hr24 = 0
                else:
                    hr24 = hr12
                dt = datetime(int(spn_anio.text), int(spn_mes.text), int(spn_dia.text),
                              hr24, int(spn_min.text))
            except ValueError:
                raise ErrorUsuario("Fecha u hora seleccionada inválida. / Invalid date or time.")
            if dt > datetime.now() + timedelta(minutes=1):
                raise ErrorUsuario("La fecha no puede estar en el futuro. / Date cannot be in the future.")
            return dt.isoformat(timespec="seconds")

        return obtener_ts

    def _popup_lectura_pasada(self):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        obtener_ts = self._bloque_fecha_hora(caja)

        caja.add_widget(lbl(ico("editar") + t("past_gluc", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(20), shorten=True))
        fila_val = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        entrada_val = campo(hint_text=t("placeholder_val", lang), input_filter="int",
                            input_type="number", size_hint_x=0.35, font_size=sp(15) * fs)
        momentos_disp = MOMENTOS_ES if lang == "es" else MOMENTOS_EN
        spn_mom = selector(momentos_disp[0], momentos_disp, factor_escala=fs, size_hint_x=0.65)
        fila_val.add_widget(entrada_val)
        fila_val.add_widget(spn_mom)
        caja.add_widget(fila_val)

        entrada_notas = campo(hint_text=t("placeholder_notes", lang), font_size=sp(12) * fs)
        caja.add_widget(entrada_notas)

        botones = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        b_cancel = boton(ico("cerrar") + t("cancel", lang), GRIS, factor_escala=fs)
        b_ok = boton(ico("check") + t("save_past", lang), CIAN, factor_escala=fs)
        botones.add_widget(b_cancel)
        botones.add_widget(b_ok)
        caja.add_widget(botones)

        pop = popup_tema(title=t("past_popup_title", lang), content=caja, size_hint=(0.95, 0.72),
                    separator_color=VIOLETA)

        @blindado
        def guardar_pasada(*_):
            ts_iso = obtener_ts()
            perfil = self.gestor.activo
            perfil.registrar(entrada_val.text, spn_mom.text, entrada_notas.text, ts=ts_iso)
            self.gestor.guardar()
            pop.dismiss()
            self.refrescar()

        b_ok.bind(on_release=guardar_pasada)
        b_cancel.bind(on_release=pop.dismiss)
        pop.open()

    def _popup_peso_pasado(self):
        perfil = self.gestor.activo
        if not perfil.tiene_datos_cuerpo:
            self._popup_cuerpo(perfil)   # faltan sexo y estatura
            return
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(10), spacing=dp(8))
        obtener_ts = self._bloque_fecha_hora(caja)

        caja.add_widget(lbl(ico("peso") + t("weight_kg", lang), font_size=sp(12) * fs,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None, height=dp(20), shorten=True))
        entrada_peso = campo(hint_text=t("weight_kg", lang), input_filter="float",
                             input_type="number", font_size=sp(16) * fs, height=dp(50))
        caja.add_widget(entrada_peso)
        caja.add_widget(Widget())

        botones = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        b_cancel = boton(ico("cerrar") + t("cancel", lang), GRIS, factor_escala=fs)
        b_ok = boton(ico("check") + t("save", lang), CIAN, factor_escala=fs)
        botones.add_widget(b_cancel)
        botones.add_widget(b_ok)
        caja.add_widget(botones)

        pop = popup_tema(title=t("past_weight_title", lang), content=caja, size_hint=(0.95, 0.66),
                    separator_color=VIOLETA)

        @blindado
        def guardar_peso(*_):
            ts_iso = obtener_ts()
            perfil.registrar_peso(entrada_peso.text, ts=ts_iso)
            self.gestor.guardar()
            pop.dismiss()
            self.refrescar()

        b_ok.bind(on_release=guardar_peso)
        b_cancel.bind(on_release=pop.dismiss)
        pop.open()

    def _popup_nuevo_perfil(self):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        entrada = campo(hint_text=t("profile_name_hint", lang), font_size=sp(14) * fs)
        botones = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(8))
        b_cancel = boton(ico("cerrar") + t("cancel", lang), GRIS, factor_escala=fs)
        b_ok = boton(ico("check") + t("create", lang), CIAN, factor_escala=fs)
        botones.add_widget(b_cancel)
        botones.add_widget(b_ok)
        caja.add_widget(lbl(ico("usuario") + t("new_profile_title", lang), color=colores["TEXTO_SUAVE"],
                            size_hint_y=None, height=dp(26), font_size=sp(12) * fs, shorten=True))
        caja.add_widget(entrada)
        caja.add_widget(Widget())
        caja.add_widget(botones)
        pop = popup_tema(title=t("new_user", lang), content=caja, size_hint=(0.9, 0.42),
                    separator_color=VIOLETA)

        @blindado
        def crear(*_):
            self.gestor.crear_perfil(entrada.text)
            pop.dismiss()
            self.refrescar()
            Clock.schedule_once(self._pedir_datos_cuerpo, 0.3)

        b_ok.bind(on_release=crear)
        entrada.bind(on_text_validate=crear)
        b_cancel.bind(on_release=pop.dismiss)
        pop.open()
        Clock.schedule_once(lambda dt: setattr(entrada, "focus", True), 0.2)

    def _popup_tiras(self):
        lang = self.app.idioma_actual
        fs = self.app.factor_escala_global
        colores = TEMAS[self.app.tema_actual]
        perfil = self.gestor.activo
        caja = BoxLayout(orientation="vertical", padding=dp(12), spacing=dp(10))
        entrada = campo(hint_text=t("strip_add_hint", lang), input_filter="int",
                        input_type="number", font_size=sp(18) * fs, height=dp(50))
        botones = BoxLayout(size_hint_y=None, height=dp(46), spacing=dp(6))
        b_cancel = boton(t("cancel", lang), GRIS, factor_escala=fs)
        b_set = boton(t("strip_set_total", lang), AZUL, factor_escala=fs)
        b_ok = boton(ico("mas") + t("add_strips", lang), CIAN, factor_escala=fs)
        botones.add_widget(b_cancel)
        botones.add_widget(b_set)
        botones.add_widget(b_ok)
        caja.add_widget(lbl(ico("barcode") + t("strip_inv_prompt", lang) % perfil.tiras,
                            color=colores["TEXTO_SUAVE"], size_hint_y=None,
                            height=dp(40), font_size=sp(12) * fs, ajuste="multi"))
        caja.add_widget(entrada)
        caja.add_widget(Widget())
        caja.add_widget(botones)
        pop = popup_tema(title=t("strip_inv_title", lang), content=caja,
                    size_hint=(0.92, 0.50), separator_color=CIAN)

        def _leer():
            txt = entrada.text.strip()
            if not txt:
                raise ErrorUsuario("Escribe un número de tiras. / Enter a number of strips.")
            return int(txt)

        @blindado
        def anadir(*_):
            perfil.anadir_tiras(_leer())
            self.gestor.guardar()
            pop.dismiss()
            self.refrescar()

        @blindado
        def fijar(*_):
            perfil.establecer_tiras(_leer())
            self.gestor.guardar()
            pop.dismiss()
            self.refrescar()

        b_ok.bind(on_release=anadir)
        b_set.bind(on_release=fijar)
        entrada.bind(on_text_validate=anadir)
        b_cancel.bind(on_release=pop.dismiss)
        pop.open()


# ======================================================================
# 5. APLICACIÓN
# ======================================================================

class CipherGlucoseApp(App):
    title = "Control de Glucosa - Cipher"

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.tema_actual = "dark"
        self.idioma_actual = "es"
        self.factor_escala_global = 1.25
        self.formato_24h = True
        self.aviso_aceptado = False

    def ciclar_zoom(self):
        i = min(range(len(ZOOMS)), key=lambda k: abs(ZOOMS[k] - self.factor_escala_global))
        self.factor_escala_global = ZOOMS[(i + 1) % len(ZOOMS)]

        if self.root:
            self.root.actualizar_estilos()

    def on_start(self):
        Clock.schedule_once(lambda *_: pedir_permisos_android(), 1.5)

    def build(self):
        Window.softinput_mode = "below_target"

        pref_path = os.path.join(self.user_data_dir, "preferencias.json")
        if os.path.exists(pref_path):
            try:
                with open(pref_path, "r", encoding="utf-8") as f:
                    prefs = json.load(f)
                tema = prefs.get("tema", "dark")
                idioma = prefs.get("idioma", "es")
                zoom = prefs.get("zoom", 1.25)
                self.tema_actual = tema if tema in TEMAS else "dark"
                self.idioma_actual = idioma if idioma in TEXTOS else "es"
                self.factor_escala_global = zoom if zoom in ZOOMS else 1.25
                self.formato_24h = bool(prefs.get("formato_24h", True))
                self.aviso_aceptado = prefs.get("aviso_v") == AVISO_VERSION
            except Exception:
                pass

        Window.clearcolor = TEMAS[self.tema_actual]["BG"]
        ruta = os.path.join(self.user_data_dir, "glucosa_datos.json")
        self.gestor = GestorGlucosa(ruta)
        self.gestor.cargar()
        return PantallaPrincipal(self.gestor, self)

    def guardar_preferencias(self):
        try:
            pref_path = os.path.join(self.user_data_dir, "preferencias.json")
            with open(pref_path, "w", encoding="utf-8") as f:
                json.dump({
                    "tema": self.tema_actual,
                    "idioma": self.idioma_actual,
                    "zoom": self.factor_escala_global,
                    "formato_24h": self.formato_24h,
                    "aviso_v": AVISO_VERSION if self.aviso_aceptado else ""
                }, f)
        except Exception:
            pass

    def _guardar_seguro(self):
        try:
            self.gestor.guardar()
            self.guardar_preferencias()
        except Exception:
            traceback.print_exc()

    def on_pause(self):
        self._guardar_seguro()
        return True

    def on_stop(self):
        self._guardar_seguro()


if __name__ == "__main__":
    CipherGlucoseApp().run()
