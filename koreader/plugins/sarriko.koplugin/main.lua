local WidgetContainer = require("ui/widget/container/widgetcontainer")
local VerticalGroup = require("ui/widget/verticalgroup")
local HorizontalGroup = require("ui/widget/horizontalgroup")
local CenterContainer = require("ui/widget/container/centercontainer")
local FrameContainer = require("ui/widget/container/framecontainer")
local TextWidget = require("ui/widget/textwidget")
local Button = require("ui/widget/button")
local UIManager = require("ui/uimanager")
local Screen = require("device").screen
local Geom = require("ui/geometry")
local Font = require("ui/font")
local Blitbuffer = require("ffi/blitbuffer")
local _ = require("gettext")

local SarrikoCalc = WidgetContainer:extend({
    name = "sarriko",
})

local VAR_NAMES = { "x", "y", "z", "a", "b", "c" }

local function gcd(a, b)
    a, b = math.abs(math.floor(a)), math.abs(math.floor(b))
    while b ~= 0 do
        a, b = b, a % b
    end
    return a == 0 and 1 or a
end

local function to_frac_str(val)
    if type(val) ~= "number" or val ~= val or math.abs(val) == math.huge then
        return "Error"
    end
    if math.abs(val) < 1e-11 then
        return "0"
    end
    local sign = val < 0 and "-" or ""
    local x = math.abs(val)
    if math.abs(x - math.floor(x + 0.5)) < 1e-7 then
        return sign .. tostring(math.floor(x + 0.5))
    end
    local h1, h2, k1, k2 = 1, 0, 0, 1
    local b = x
    for _ = 1, 15 do
        local a = math.floor(b)
        local h = a * h1 + h2
        local k = a * k1 + k2
        if k > 9999 then break end
        h2, h1 = h1, h
        k2, k1 = k1, k
        if math.abs(x - (h1 / k1)) < 1e-7 then
            local g = gcd(h1, k1)
            return string.format("%.4g (%s%d/%d)", val, sign, math.floor(h1 / g), math.floor(k1 / g))
        end
        local rem = b - a
        if rem < 1e-10 then break end
        b = 1 / rem
    end
    return string.format("%.6g", val)
end

-- Aritmética compleja para ecuaciones de 2º, 3º y 4º grado
local function c_new(r, i) return { r = r or 0, i = i or 0 } end
local function c_add(a, b) return { r = a.r + b.r, i = a.i + b.i } end
local function c_sub(a, b) return { r = a.r - b.r, i = a.i - b.i } end
local function c_mul(a, b) return { r = a.r * b.r - a.i * b.i, i = a.r * b.i + a.i * b.r } end
local function c_abs(a) return math.sqrt(a.r * a.r + a.i * a.i) end

local function c_div(a, b)
    local d = b.r * b.r + b.i * b.i
    if d == 0 then return { r = 0, i = 0 } end
    return { r = (a.r * b.r + a.i * b.i) / d, i = (a.i * b.r - a.r * b.i) / d }
end

local function c_sqrt(a)
    local m = c_abs(a)
    if m == 0 then return { r = 0, i = 0 } end
    local r = math.sqrt(math.max(0, (m + a.r) / 2))
    local i = math.sqrt(math.max(0, (m - a.r) / 2))
    if a.i < 0 then i = -i end
    return { r = r, i = i }
end

local function c_format(z)
    local r = math.abs(z.r) < 1e-7 and 0 or z.r
    local i = math.abs(z.i) < 1e-7 and 0 or z.i
    if i == 0 then
        return to_frac_str(r)
    elseif r == 0 then
        return string.format("%.4gi", i)
    else
        local sign = i > 0 and "+" or "-"
        return string.format("%.4g %s %.4gi", r, sign, math.abs(i))
    end
end

-- Funciones matemáticas auxiliares para Distribuciones de Probabilidad
local SQRT_2PI = math.sqrt(2 * math.pi)

local function norm_pdf(z)
    return math.exp(-0.5 * z * z) / SQRT_2PI
end

local function norm_cdf(z)
    local sign = 1
    if z < 0 then
        sign = -1
        z = -z
    end
    local t = 1.0 / (1.0 + 0.2316419 * z)
    local poly = t * (0.319381530 + t * (-0.356563782 + t * (1.781477937 + t * (-1.821255978 + 1.330274429 * t))))
    local pdf = norm_pdf(z)
    local cdf_pos = 1.0 - pdf * poly
    if sign == 1 then
        return cdf_pos
    else
        return 1.0 - cdf_pos
    end
end

local function norm_inv(p)
    if p <= 0 or p >= 1 then return 0 end
    -- Semilla inicial de Beasley-Springer-Moro + refinamiento Newton-Raphson
    local q = p - 0.5
    local z
    if math.abs(q) <= 0.425 then
        local r = 0.180625 - q * q
        z = q * (((((((2509.0809287301226727 * r + 33430.575583588128105) * r + 67265.770927008700853) * r
            + 45921.953931549871457) * r + 13731.693765509461125) * r + 1971.5909503065514427) * r
            + 133.14166789178437745) * r + 3.387132872796366608)
            / (((((((5226.495278852854561 * r + 28729.085735721942674) * r + 39307.89580009271061) * r
            + 21213.794301586595867) * r + 5394.1960214247511077) * r + 687.1870074920579083) * r
            + 42.313330701600911252) * r + 1.0)
    else
        local r = (q < 0) and p or (1.0 - p)
        r = math.sqrt(-math.log(r))
        z = (((2.32121276858 * r + 4.85014127135) * r - 2.29796479134) * r - 2.78718931138)
            / ((1.63706781897 * r + 3.54388924762) * r + 1.0)
        if q < 0 then z = -z end
    end
    for _ = 1, 3 do
        local err = norm_cdf(z) - p
        local d = norm_pdf(z)
        if d > 1e-14 then
            z = z - err / d
        end
    end
    return z
end

local function log_fact(n)
    if n <= 1 then return 0 end
    if n <= 30 then
        local s = 0
        for i = 2, n do s = s + math.log(i) end
        return s
    end
    -- Fórmula de Stirling de alta precisión para n > 30
    local x = n + 1
    return (x - 0.5) * math.log(x) - x + 0.5 * math.log(2 * math.pi) + 1.0 / (12.0 * x) - 1.0 / (360.0 * x * x * x)
end

local function binom_pmf(n, k, p)
    if k < 0 or k > n then return 0 end
    if p <= 0 then return (k == 0) and 1 or 0 end
    if p >= 1 then return (k == n) and 1 or 0 end
    local ln_comb = log_fact(n) - log_fact(k) - log_fact(n - k)
    local ln_prob = ln_comb + k * math.log(p) + (n - k) * math.log(1 - p)
    return math.exp(ln_prob)
end

local function pois_pmf(lambda, k)
    if k < 0 or lambda <= 0 then return (k == 0 and lambda == 0) and 1 or 0 end
    local ln_prob = -lambda + k * math.log(lambda) - log_fact(k)
    return math.exp(ln_prob)
end

-- Modos financieros y de distribuciones
local FIN_MODES = {
    cap = {
        {
            id = "comp",
            name = "Kap. Konposatua",
            formula = "Cn = C0*(1+i)^n  |  C0 = Cn*(1+i)^(-n)  |  Cn = C0*(1+i)^m*(1+θ*i)",
            fields = {
                { k = "C0", label = "C0 (Kapital hasiera)", def = "1000" },
                { k = "i", label = "i (Interesa, ej: 0.05)", def = "0.05" },
                { k = "n", label = "n (Aldiak / Años)", def = "3" },
                { k = "theta", label = "θ (Fracción año, 0=no)", def = "0" },
            },
        },
        {
            id = "simp",
            name = "Bakuna & Deskontua",
            formula = "Cn = C0*(1+n*i)  |  Dr = Cn*n*i/(1+n*i)  |  L = N*(1-n*d) - N*g - k",
            fields = {
                { k = "C", label = "C0 o Nominal N", def = "1000" },
                { k = "i", label = "i o d (Tanto, ej: 0.06)", def = "0.06" },
                { k = "n", label = "n (Tiempo, ej: 0.5)", def = "1" },
                { k = "g", label = "g (Comisión %, ej: 0.01)", def = "0" },
                { k = "k", label = "k (Gasto fijo €)", def = "0" },
            },
        },
        {
            id = "equiv",
            name = "Tantos: i, ik, Jk, d",
            formula = "i = (1+ik)^k - 1  |  Jk = k*ik  |  (1+i)*(1-d) = 1",
            fields = {
                { k = "i", label = "i efectivo anual (0 si usas ik)", def = "0.06" },
                { k = "ik", label = "ik fraccionado (0 si usas i)", def = "0" },
                { k = "k", label = "k (Frecuencia: 12 mes, 4 trim)", def = "12" },
            },
        },
        {
            id = "venc",
            name = "Mugaegun Batezbest.",
            formula = "C = ∑Ci  |  n_medio = (∑Ci*ti) / ∑Ci",
            fields = {
                { k = "C1", label = "C1 (Kapital 1)", def = "1000" },
                { k = "t1", label = "t1 (Vencim. 1)", def = "1" },
                { k = "C2", label = "C2 (Kapital 2)", def = "2000" },
                { k = "t2", label = "t2 (Vencim. 2)", def = "3" },
                { k = "C3", label = "C3 (Kapital 3)", def = "3000" },
                { k = "t3", label = "t3 (Vencim. 3)", def = "5" },
            },
        },
    },
    rent = {
        {
            id = "const",
            name = "Constante (a_n|i)",
            formula = "Va = M*(1-(1+i)^(-n))/i  |  Vs = M*((1+i)^n - 1)/i  |  Perp = M/i",
            fields = {
                { k = "M", label = "M (Término / Cuota)", def = "500" },
                { k = "i", label = "i (Tanto interés)", def = "0.04" },
                { k = "n", label = "n (Nº de periodos)", def = "10" },
                { k = "k", label = "k (Fraccionam. 1=no)", def = "1" },
            },
        },
        {
            id = "arit",
            name = "Aritmética A(M,π)",
            formula = "A(M1,π) = (M1 + π/i)*a_n|i - (n*π*V^n)/i  |  Perp = (M1 + π/i)/i",
            fields = {
                { k = "M1", label = "M1 (Primera cuota)", def = "500" },
                { k = "pi", label = "π (Variación lineal)", def = "50" },
                { k = "i", label = "i (Tanto interés)", def = "0.04" },
                { k = "n", label = "n (Nº de periodos)", def = "10" },
            },
        },
        {
            id = "geom",
            name = "Geométrica A(M,q)",
            formula = "Si 1+i≠q: M1*(1-q^n*V^n)/(1+i-q)  |  Si 1+i=q: M1*n*V",
            fields = {
                { k = "M1", label = "M1 (Primera cuota)", def = "500" },
                { k = "q", label = "q (Razón, ej: 1.03)", def = "1.03" },
                { k = "i", label = "i (Tanto interés)", def = "0.04" },
                { k = "n", label = "n (Nº de periodos)", def = "10" },
            },
        },
    },
    loan = {
        {
            id = "frances",
            name = "Mailegu Francés",
            formula = "P = M*a_n|i  |  Dt = M*a_(n-t)|i  |  It = D(t-1)*i  |  At = A1*(1+i)^(t-1)",
            fields = {
                { k = "P", label = "P (Préstamo inicial)", def = "10000" },
                { k = "i", label = "i (Interés periodo)", def = "0.05" },
                { k = "n", label = "n (Periodos totales)", def = "10" },
                { k = "t", label = "t (Periodo a consultar)", def = "4" },
            },
        },
        {
            id = "ital_amer",
            name = "Italiano & Americano",
            formula = "Italiano: A = P/n, Dt = (n-t)*A  |  Americano: It = P*i + Fondo Sinking",
            fields = {
                { k = "P", label = "P (Préstamo inicial)", def = "10000" },
                { k = "i", label = "i (Interés préstamo)", def = "0.05" },
                { k = "n", label = "n (Periodos totales)", def = "10" },
                { k = "t", label = "t (Periodo a consultar)", def = "4" },
                { k = "ifondo", label = "i_fondo (Solo Americano)", def = "0.03" },
            },
        },
        {
            id = "eraketa",
            name = "Eraketak (Constit.)",
            formula = "C = M * s̈_n|i  |  Ft = M * s̈_t|i  |  Reserva Pt = C - Ft",
            fields = {
                { k = "C", label = "C (Capital objetivo)", def = "20000" },
                { k = "i", label = "i (Interés periodo)", def = "0.04" },
                { k = "n", label = "n (Plazo total)", def = "8" },
                { k = "t", label = "t (Periodo actual)", def = "3" },
            },
        },
        {
            id = "vantir",
            name = "VAN y TIR (Extra)",
            formula = "VAN = -I0 + ∑ Qj*(1+k)^(-j)  |  TIR: tasa r donde VAN(r) = 0",
            fields = {
                { k = "I0", label = "I0 (Desembolso inicial)", def = "1000" },
                { k = "k", label = "k (Tasa descuento VAN)", def = "0.08" },
                { k = "Q1", label = "Q1 (Flujo año 1)", def = "400" },
                { k = "Q2", label = "Q2 (Flujo año 2)", def = "400" },
                { k = "Q3", label = "Q3 (Flujo año 3)", def = "400" },
                { k = "Q4", label = "Q4 (Flujo año 4)", def = "200" },
            },
        },
    },
}

local DIST_MODES = {
    [3] = {
        id = "normal",
        name = "Normal",
        formula = "X ~ N(μ, σ)  |  Z = (x - μ)/σ  |  Φ(z) = P(Z ≤ z)  |  Inv: P(X ≤ xp) = p",
        fields = {
            { k = "mu", label = "μ (Media poblacional)", def = "0" },
            { k = "sigma", label = "σ (Desviación típica)", def = "1" },
            { k = "x", label = "x (Valor a evaluar)", def = "1.96" },
            { k = "x1", label = "x1 (Lím. inf. intervalo)", def = "-1.96" },
            { k = "p", label = "p (Prob. para Inversa)", def = "0.975" },
        },
    },
    [4] = {
        id = "binomial",
        name = "Binomial",
        formula = "X ~ B(n, p)  |  P(X=k) = C(n,k)·p^k·(1-p)^(n-k)  |  E[X]=np, V[X]=npq",
        fields = {
            { k = "n", label = "n (Nº de ensayos)", def = "10" },
            { k = "p", label = "p (Prob. éxito 0..1)", def = "0.4" },
            { k = "k", label = "k (Éxitos a evaluar)", def = "4" },
            { k = "k1", label = "k1 (Lím. inf. intervalo)", def = "2" },
        },
    },
    [5] = {
        id = "poisson",
        name = "Poisson",
        formula = "X ~ Pois(λ)  |  P(X=k) = e^(-λ)·λ^k / k!  |  E[X] = V[X] = λ",
        fields = {
            { k = "lambda", label = "λ (Tasa media ocurren.)", def = "3.5" },
            { k = "k", label = "k (Ocurrencias a eval.)", def = "3" },
            { k = "k1", label = "k1 (Lím. inf. intervalo)", def = "1" },
        },
    },
}

function SarrikoCalc:init()
    self.tab = "poly" -- "poly", "sys", "cap", "rent", "loan", "stat"
    self.show_formula = true
    self.fresh_field = true
    self.window = nil

    -- 1. Polinomios (Grado 2, 3, 4)
    self.poly_deg = 2
    self.poly_coeffs = { "1", "-5", "6", "0", "0" }
    self.poly_sel = 1

    -- 2. Sistemas Lineales NxN (2x2 hasta 6x6: x, y, z, a, b, c)
    self.sys_n = 2
    self.sys_eq = 1
    self.sys_col = 1
    self.sys_mat = {}
    for r = 1, 6 do
        self.sys_mat[r] = {}
        for c = 1, 7 do
            self.sys_mat[r][c] = (r == c) and "1" or ((c == 7) and tostring(r) or "0")
        end
    end

    -- 3. Finanzas Sarriko
    self.fin_sub = { cap = 1, rent = 1, loan = 1 }
    self.fin_vals = {}
    self.fin_sel = 1
    self:_initFinDefaults()

    -- 4. Estadística y Probabilidad (Submodos: 1=1-Var, 2=2-Var Reg, 3=Normal, 4=Binomial, 5=Poisson)
    self.stat_sub = 1
    self.stat1_n = 5
    self.stat1_mode = "x" -- "x" edita valores xi, "f" edita frecuencias ni
    self.stat1_sel = 1
    self.stat1_x = { "10", "12", "15", "18", "20", "22", "25", "30" }
    self.stat1_f = { "1", "2", "4", "2", "1", "1", "1", "1" }

    self.stat2_n = 4
    self.stat2_mode = "x" -- "x" edita X, "y" edita Y, "x0" edita punto a predecir
    self.stat2_sel = 1
    self.stat2_x = { "1", "2", "3", "4", "5", "6" }
    self.stat2_y = { "2.5", "4.1", "5.8", "8.2", "9.9", "11.5" }
    self.stat2_x0 = "5"

    self.dist_vals = {}
    self.dist_sel = 1
    for k_idx, d_def in pairs(DIST_MODES) do
        self.dist_vals[k_idx] = {}
        for _, f in ipairs(d_def.fields) do
            self.dist_vals[k_idx][f.k] = f.def
        end
    end

    self.result_lines = {}
    self:_recalculate()

    self.ui.menu:registerToMainMenu(self)
end

function SarrikoCalc:addToMainMenu(menu_items)
    menu_items.sarriko = {
        text = _("Calculadora Financiera, Álgebra y Estadística"),
        sorting_hint = "tools",
        callback = function()
            self:show()
        end,
    }
end

function SarrikoCalc:_initFinDefaults()
    for cat, list in pairs(FIN_MODES) do
        self.fin_vals[cat] = {}
        for m_idx, m in ipairs(list) do
            self.fin_vals[cat][m_idx] = {}
            for _, f in ipairs(m.fields) do
                self.fin_vals[cat][m_idx][f.k] = f.def
            end
        end
    end
end

function SarrikoCalc:_makeText(text, font_size)
    return TextWidget:new({
        text = text,
        face = Font:getFace("cfont", font_size or 16),
    })
end

function SarrikoCalc:_makeButton(text, callback, width, height, bordersize)
    return Button:new({
        text = text,
        callback = function()
            callback()
        end,
        width = width,
        height = height,
        bordersize = bordersize or 2,
        radius = 0,
        margin = 1,
        padding = 1,
    })
end

function SarrikoCalc:_closeWindow(is_exiting)
    if self.window then
        UIManager:close(self.window)
        self.window = nil
        if is_exiting then
            UIManager:setDirty("all", "ui")
        end
    end
end

function SarrikoCalc:_getActiveString()
    if self.tab == "poly" then
        return self.poly_coeffs[self.poly_sel] or "0"
    elseif self.tab == "sys" then
        return self.sys_mat[self.sys_eq][self.sys_col] or "0"
    elseif self.tab == "stat" then
        if self.stat_sub == 1 then
            local arr = (self.stat1_mode == "x") and self.stat1_x or self.stat1_f
            return arr[self.stat1_sel] or "0"
        elseif self.stat_sub == 2 then
            if self.stat2_mode == "x0" then return self.stat2_x0 end
            local arr = (self.stat2_mode == "x") and self.stat2_x or self.stat2_y
            return arr[self.stat2_sel] or "0"
        else
            local d_def = DIST_MODES[self.stat_sub]
            local f_def = d_def.fields[self.dist_sel] or d_def.fields[1]
            return self.dist_vals[self.stat_sub][f_def.k] or "0"
        end
    else
        local sub_idx = self.fin_sub[self.tab]
        local mode_def = FIN_MODES[self.tab][sub_idx]
        local field_def = mode_def.fields[self.fin_sel] or mode_def.fields[1]
        return self.fin_vals[self.tab][sub_idx][field_def.k] or "0"
    end
end

function SarrikoCalc:_setActiveString(str)
    if self.tab == "poly" then
        self.poly_coeffs[self.poly_sel] = str
    elseif self.tab == "sys" then
        self.sys_mat[self.sys_eq][self.sys_col] = str
    elseif self.tab == "stat" then
        if self.stat_sub == 1 then
            local arr = (self.stat1_mode == "x") and self.stat1_x or self.stat1_f
            arr[self.stat1_sel] = str
        elseif self.stat_sub == 2 then
            if self.stat2_mode == "x0" then
                self.stat2_x0 = str
            else
                local arr = (self.stat2_mode == "x") and self.stat2_x or self.stat2_y
                arr[self.stat2_sel] = str
            end
        else
            local d_def = DIST_MODES[self.stat_sub]
            local f_def = d_def.fields[self.dist_sel] or d_def.fields[1]
            self.dist_vals[self.stat_sub][f_def.k] = str
        end
    else
        local sub_idx = self.fin_sub[self.tab]
        local mode_def = FIN_MODES[self.tab][sub_idx]
        local field_def = mode_def.fields[self.fin_sel] or mode_def.fields[1]
        self.fin_vals[self.tab][sub_idx][field_def.k] = str
    end
end

function SarrikoCalc:_onKeyPress(key)
    local cur = self:_getActiveString()
    if key == "CLR" then
        self:_setActiveString("0")
        self.fresh_field = true
    elseif key == "DEL" then
        if #cur <= 1 or (cur == "-0") or (#cur == 2 and string.sub(cur, 1, 1) == "-") then
            self:_setActiveString("0")
            self.fresh_field = true
        else
            self:_setActiveString(string.sub(cur, 1, -2))
        end
    elseif key == "+/-" then
        if string.sub(cur, 1, 1) == "-" then
            self:_setActiveString(string.sub(cur, 2))
        elseif cur ~= "0" then
            self:_setActiveString("-" .. cur)
        end
    elseif key == "." then
        if self.fresh_field then
            self:_setActiveString("0.")
            self.fresh_field = false
        elseif not string.find(cur, "%.") then
            self:_setActiveString(cur .. ".")
        end
    elseif key == "NEXT" then
        self:_advanceField()
    else
        if self.fresh_field or cur == "0" then
            self:_setActiveString(key)
            self.fresh_field = false
        else
            self:_setActiveString(cur .. key)
        end
    end
    self:_recalculate()
    self:show()
end

function SarrikoCalc:_advanceField()
    self.fresh_field = true
    if self.tab == "poly" then
        self.poly_sel = (self.poly_sel % (self.poly_deg + 1)) + 1
    elseif self.tab == "sys" then
        if self.sys_col < self.sys_n + 1 then
            self.sys_col = self.sys_col + 1
        else
            self.sys_col = 1
            self.sys_eq = (self.sys_eq % self.sys_n) + 1
        end
    elseif self.tab == "stat" then
        if self.stat_sub == 1 then
            self.stat1_sel = (self.stat1_sel % self.stat1_n) + 1
        elseif self.stat_sub == 2 then
            if self.stat2_mode ~= "x0" then
                self.stat2_sel = (self.stat2_sel % self.stat2_n) + 1
            end
        else
            local n_f = #DIST_MODES[self.stat_sub].fields
            self.dist_sel = (self.dist_sel % n_f) + 1
        end
    else
        local sub_idx = self.fin_sub[self.tab]
        local n_fields = #FIN_MODES[self.tab][sub_idx].fields
        self.fin_sel = (self.fin_sel % n_fields) + 1
    end
end

-- RESOLUCIÓN ANALÍTICA DE ECUACIONES DE 2º, 3º Y 4º GRADO
function SarrikoCalc:_solveQuadComplex(A, B, C)
    local fourAC = c_mul(c_new(4, 0), c_mul(A, C))
    local disc = c_sub(c_mul(B, B), fourAC)
    local sq = c_sqrt(disc)
    local twoA = c_mul(c_new(2, 0), A)
    local r1 = c_div(c_add(c_new(-B.r, -B.i), sq), twoA)
    local r2 = c_div(c_sub(c_new(-B.r, -B.i), sq), twoA)
    return r1, r2
end

function SarrikoCalc:_solveCubicReal(a, b, c, d)
    if math.abs(a) < 1e-12 then
        local r1, r2 = self:_solveQuadComplex(c_new(b, 0), c_new(c, 0), c_new(d, 0))
        return { r1, r2 }
    end
    local A, B, C = b / a, c / a, d / a
    local shift = A / 3
    local p = B - (A * A) / 3
    local q = (2 * A * A * A) / 27 - (A * B) / 3 + C
    local disc = (q / 2) * (q / 2) + (p / 3) * (p / 3) * (p / 3)

    if math.abs(p) < 1e-12 and math.abs(q) < 1e-12 then
        local r = c_new(-shift, 0)
        return { r, r, r }
    elseif disc > 1e-12 then
        local sq = math.sqrt(disc)
        local u_val = -q / 2 + sq
        local v_val = -q / 2 - sq
        local u = (u_val >= 0 and 1 or -1) * (math.abs(u_val) ^ (1 / 3))
        local v = (v_val >= 0 and 1 or -1) * (math.abs(v_val) ^ (1 / 3))
        local y1 = u + v
        local real_part = -(u + v) / 2 - shift
        local imag_part = (math.sqrt(3) / 2) * (u - v)
        return {
            c_new(y1 - shift, 0),
            c_new(real_part, imag_part),
            c_new(real_part, -imag_part),
        }
    else
        local r = math.sqrt(math.max(0, -(p * p * p) / 27))
        local phi = 0
        if r > 1e-12 then
            local arg = math.max(-1, math.min(1, (-q / 2) / r))
            phi = math.acos(arg)
        end
        local m = 2 * (r ^ (1 / 3))
        local y1 = m * math.cos(phi / 3) - shift
        local y2 = m * math.cos((phi + 2 * math.pi) / 3) - shift
        local y3 = m * math.cos((phi + 4 * math.pi) / 3) - shift
        return { c_new(y1, 0), c_new(y2, 0), c_new(y3, 0) }
    end
end

function SarrikoCalc:_solveQuarticReal(a, b, c, d, e)
    if math.abs(a) < 1e-12 then
        return self:_solveCubicReal(b, c, d, e)
    end
    local A, B, C, D = b / a, c / a, d / a, e / a
    local shift = A / 4
    local p = B - (3 * A * A) / 8
    local q = (A * A * A) / 8 - (A * B) / 2 + C
    local r = -(3 * A * A * A * A) / 256 + (A * A * B) / 16 - (A * C) / 4 + D

    if math.abs(q) < 1e-10 then
        local u1, u2 = self:_solveQuadComplex(c_new(1, 0), c_new(p, 0), c_new(r, 0))
        local s1 = c_sqrt(u1)
        local s2 = c_sqrt(u2)
        return {
            c_new(s1.r - shift, s1.i),
            c_new(-s1.r - shift, -s1.i),
            c_new(s2.r - shift, s2.i),
            c_new(-s2.r - shift, -s2.i),
        }
    end

    local cub_roots = self:_solveCubicReal(1, 2 * p, p * p - 4 * r, -q * q)
    local z_pick = cub_roots[1]
    for _, cr in ipairs(cub_roots) do
        if c_abs(cr) > c_abs(z_pick) then
            z_pick = cr
        end
    end

    local u = c_sqrt(z_pick)
    local P_c = c_new(p, 0)
    local Q_c = c_new(q, 0)
    local q_over_u = c_div(Q_c, u)
    local v = c_div(c_sub(c_add(P_c, z_pick), q_over_u), c_new(2, 0))
    local w = c_div(c_add(c_add(P_c, z_pick), q_over_u), c_new(2, 0))

    local y1, y2 = self:_solveQuadComplex(c_new(1, 0), u, v)
    local y3, y4 = self:_solveQuadComplex(c_new(1, 0), c_new(-u.r, -u.i), w)

    return {
        c_new(y1.r - shift, y1.i),
        c_new(y2.r - shift, y2.i),
        c_new(y3.r - shift, y3.i),
        c_new(y4.r - shift, y4.i),
    }
end

function SarrikoCalc:_calcPolynomial()
    local a = tonumber(self.poly_coeffs[1]) or 0
    local b = tonumber(self.poly_coeffs[2]) or 0
    local c = tonumber(self.poly_coeffs[3]) or 0
    local d = tonumber(self.poly_coeffs[4]) or 0
    local e = tonumber(self.poly_coeffs[5]) or 0

    if math.abs(a) < 1e-12 then
        self.result_lines = { _("El coeficiente principal 'a' no puede ser 0.") }
        return
    end

    if self.poly_deg == 2 then
        local disc = b * b - 4 * a * c
        local r1, r2 = self:_solveQuadComplex(c_new(a, 0), c_new(b, 0), c_new(c, 0))
        local vx = -b / (2 * a)
        local vy = a * vx * vx + b * vx + c
        self.result_lines = {
            string.format("Δ = b² - 4ac = %.4g   |   Vértice: (%.4g, %.4g)", disc, vx, vy),
            string.format("x1 = %s", c_format(r1)),
            string.format("x2 = %s", c_format(r2)),
        }
    elseif self.poly_deg == 3 then
        local roots = self:_solveCubicReal(a, b, c, d)
        self.result_lines = {
            string.format("x1 = %s", c_format(roots[1])),
            string.format("x2 = %s", c_format(roots[2])),
            string.format("x3 = %s", c_format(roots[3] or c_new(0, 0))),
        }
    else
        local roots = self:_solveQuarticReal(a, b, c, d, e)
        self.result_lines = {
            string.format("x1 = %s   |   x2 = %s", c_format(roots[1]), c_format(roots[2])),
            string.format("x3 = %s   |   x4 = %s", c_format(roots[3]), c_format(roots[4])),
        }
    end
end

-- RESOLUCIÓN DE SISTEMAS LINEALES NxN
function SarrikoCalc:_calcLinearSystem()
    local n = self.sys_n
    local A = {}
    for r = 1, n do
        A[r] = {}
        for c = 1, n do
            A[r][c] = tonumber(self.sys_mat[r][c]) or 0
        end
        A[r][n + 1] = tonumber(self.sys_mat[r][7]) or 0
    end

    local det = 1
    for col = 1, n do
        local pivot = col
        local max_v = math.abs(A[col][col])
        for row = col + 1, n do
            if math.abs(A[row][col]) > max_v then
                max_v = math.abs(A[row][col])
                pivot = row
            end
        end

        if max_v < 1e-11 then
            self.result_lines = {
                _("det(A) = 0  →  Sistema Singular (Incompatible o Indeterminado)."),
            }
            return
        end

        if pivot ~= col then
            A[col], A[pivot] = A[pivot], A[col]
            det = -det
        end

        det = det * A[col][col]

        for row = col + 1, n do
            local factor = A[row][col] / A[col][col]
            for k = col, n + 1 do
                A[row][k] = A[row][k] - factor * A[col][k]
            end
        end
    end

    local sol = {}
    for row = n, 1, -1 do
        local sum = A[row][n + 1]
        for col = row + 1, n do
            sum = sum - A[row][col] * sol[col]
        end
        sol[row] = sum / A[row][row]
    end

    local line1, line2 = {}, {}
    for i = 1, n do
        local item = string.format("%s = %s", VAR_NAMES[i], to_frac_str(sol[i]))
        if i <= 3 then
            table.insert(line1, item)
        else
            table.insert(line2, item)
        end
    end

    self.result_lines = {
        string.format("Sistema Compatible Determinado   |   det(A) = %.5g", det),
        table.concat(line1, "    |    "),
    }
    if #line2 > 0 then
        table.insert(self.result_lines, table.concat(line2, "    |    "))
    end
end

-- CÁLCULOS DE ESTADÍSTICA (1-VAR, 2-VAR) Y DISTRIBUCIONES (NORMAL, BINOMIAL, POISSON)
function SarrikoCalc:_calcStatistics()
    if self.stat_sub == 1 then
        -- 1-Variable con frecuencias (xi, ni)
        local pairs_list = {}
        local N = 0
        local sum_x = 0
        local sum_x2 = 0

        for i = 1, self.stat1_n do
            local xi = tonumber(self.stat1_x[i]) or 0
            local ni = math.max(0, tonumber(self.stat1_f[i]) or 0)
            if ni > 0 then
                N = N + ni
                sum_x = sum_x + xi * ni
                sum_x2 = sum_x2 + (xi * xi) * ni
                table.insert(pairs_list, { x = xi, n = ni })
            end
        end

        if N <= 0 then
            self.result_lines = { _("La suma de frecuencias N debe ser mayor que 0.") }
            return
        end

        local mean = sum_x / N
        local var_pop = math.max(0, (sum_x2 / N) - (mean * mean))
        local sd_pop = math.sqrt(var_pop)
        local var_samp = (N > 1) and (var_pop * N / (N - 1)) or 0
        local sd_samp = math.sqrt(var_samp)
        local cv = (math.abs(mean) > 1e-12) and ((sd_pop / math.abs(mean)) * 100) or 0

        table.sort(pairs_list, function(a, b) return a.x < b.x end)
        local half = N / 2.0
        local cum = 0
        local median = pairs_list[1].x
        for idx, item in ipairs(pairs_list) do
            cum = cum + item.n
            if cum > half then
                median = item.x
                break
            elseif math.abs(cum - half) < 1e-9 and pairs_list[idx + 1] then
                median = 0.5 * (item.x + pairs_list[idx + 1].x)
                break
            end
        end

        self.result_lines = {
            string.format("N = %.4g  |  ∑x·n = %.5g  |  ∑x²·n = %.6g  |  Mediana = %.5g", N, sum_x, sum_x2, median),
            string.format("Media x̄ = %.6g   |   Varianza σ² = %.6g   |   Cuasivar. S² = %.6g", mean, var_pop, var_samp),
            string.format("Desv. Típica σ = %.6g   |   Cuasidesv. S = %.6g   |   CV = %.2f%%", sd_pop, sd_samp, cv),
        }

    elseif self.stat_sub == 2 then
        -- 2-Variables y Regresión Lineal (Y = a + b·X)
        local n = self.stat2_n
        local sx, sy, sxx, syy, sxy = 0, 0, 0, 0, 0
        for i = 1, n do
            local xi = tonumber(self.stat2_x[i]) or 0
            local yi = tonumber(self.stat2_y[i]) or 0
            sx = sx + xi
            sy = sy + yi
            sxx = sxx + xi * xi
            syy = syy + yi * yi
            sxy = sxy + xi * yi
        end

        local mx = sx / n
        local my = sy / n
        local vx = math.max(0, (sxx / n) - mx * mx)
        local vy = math.max(0, (syy / n) - my * my)
        local sdx = math.sqrt(vx)
        local sdy = math.sqrt(vy)
        local cov = (sxy / n) - mx * my

        local b_slope = (vx > 1e-12) and (cov / vx) or 0
        local a_inter = my - b_slope * mx
        local r_corr = (sdx > 1e-12 and sdy > 1e-12) and (cov / (sdx * sdy)) or 0
        local r2 = r_corr * r_corr
        local x0 = tonumber(self.stat2_x0) or 0
        local y_pred = a_inter + b_slope * x0

        self.result_lines = {
            string.format("x̄ = %.5g (σx = %.4g)  |  ȳ = %.5g (σy = %.4g)  |  Cov σxy = %.5g", mx, sdx, my, sdy, cov),
            string.format("Correlación r = %.5f   |   Bondad ajuste R² = %.5f (%.2f%%)", r_corr, r2, r2 * 100),
            string.format("Recta: y = %.5g %s %.5g·x   |   Si x0=%.4g → ŷ = %.5g",
                a_inter, b_slope >= 0 and "+" or "-", math.abs(b_slope), x0, y_pred),
        }

    elseif self.stat_sub == 3 then
        -- Distribución Normal N(μ, σ)
        local raw = self.dist_vals[3]
        local mu = tonumber(raw.mu) or 0
        local sigma = tonumber(raw.sigma) or 1
        local x = tonumber(raw.x) or 0
        local x1 = tonumber(raw.x1) or 0
        local p = tonumber(raw.p) or 0.95

        if sigma <= 0 then
            self.result_lines = { _("La desviación típica σ debe ser mayor que 0.") }
            return
        end

        local z = (x - mu) / sigma
        local z1 = (x1 - mu) / sigma
        local fx = norm_pdf(z) / sigma
        local cdf_x = norm_cdf(z)
        local tail_x = 1.0 - cdf_x
        local p_inter = math.abs(norm_cdf(z) - norm_cdf(z1))

        local inv_str
        if p > 0 and p < 1 then
            local zp = norm_inv(p)
            local xp = mu + zp * sigma
            inv_str = string.format("Inv(p=%.4g): zp = %.4f → xp = %.5g", p, zp, xp)
        else
            inv_str = "Inv: p debe estar en (0, 1)"
        end

        self.result_lines = {
            string.format("Tipificación:  z = %.5f   |   Densidad puntual f(x) = %.6f", z, fx),
            string.format("Acumulada P(X ≤ x) = %.6f   |   Cola Sup. P(X > x) = %.6f", cdf_x, tail_x),
            string.format("Intervalo P(%.4g ≤ X ≤ %.4g) = %.6f  |  %s", math.min(x1, x), math.max(x1, x), p_inter, inv_str),
        }

    elseif self.stat_sub == 4 then
        -- Distribución Binomial B(n, p)
        local raw = self.dist_vals[4]
        local n = math.floor((tonumber(raw.n) or 10) + 0.5)
        local p = tonumber(raw.p) or 0.5
        local k = math.floor((tonumber(raw.k) or 0) + 0.5)
        local k1 = math.floor((tonumber(raw.k1) or 0) + 0.5)

        if n < 1 or n > 5000 or p < 0 or p > 1 then
            self.result_lines = { _("Parámetros requeridos: 1 ≤ n ≤ 5000  y  0 ≤ p ≤ 1.") }
            return
        end

        local ex = n * p
        local vx = n * p * (1 - p)
        local sdx = math.sqrt(vx)

        local pmf_k = binom_pmf(n, k, p)
        local cdf_le = 0
        local cdf_lt = 0
        local lo, hi = math.min(k1, k), math.max(k1, k)
        local p_inter = 0

        for i = 0, n do
            local pr = binom_pmf(n, i, p)
            if i < k then cdf_lt = cdf_lt + pr end
            if i <= k then cdf_le = cdf_le + pr end
            if i >= lo and i <= hi then p_inter = p_inter + pr end
        end

        local tail_ge = math.max(0, 1.0 - cdf_lt)
        local tail_gt = math.max(0, 1.0 - cdf_le)

        self.result_lines = {
            string.format("Media E[X] = %.4g   |   Varianza V[X] = %.4g   |   Desv. σ = %.4g", ex, vx, sdx),
            string.format("Puntual P(X = %d) = %.6f   |   Intervalo P(%d ≤ X ≤ %d) = %.6f", k, pmf_k, lo, hi, p_inter),
            string.format("Acum: P(X≤%d)=%.5f | P(X<%d)=%.5f | Cola: P(X≥%d)=%.5f | P(X>%d)=%.5f",
                k, cdf_le, k, cdf_lt, k, tail_ge, k, tail_gt),
        }

    elseif self.stat_sub == 5 then
        -- Distribución de Poisson Pois(λ)
        local raw = self.dist_vals[5]
        local lambda = tonumber(raw.lambda) or 1
        local k = math.floor((tonumber(raw.k) or 0) + 0.5)
        local k1 = math.floor((tonumber(raw.k1) or 0) + 0.5)

        if lambda <= 0 or k < 0 or k > 5000 then
            self.result_lines = { _("Parámetros requeridos: λ > 0  y  0 ≤ k ≤ 5000.") }
            return
        end

        local pmf_k = pois_pmf(lambda, k)
        local cdf_le = 0
        local cdf_lt = 0
        local lo, hi = math.max(0, math.min(k1, k)), math.max(k1, k)
        local p_inter = 0

        for i = 0, math.max(k, hi) do
            local pr = pois_pmf(lambda, i)
            if i < k then cdf_lt = cdf_lt + pr end
            if i <= k then cdf_le = cdf_le + pr end
            if i >= lo and i <= hi then p_inter = p_inter + pr end
        end

        local tail_ge = math.max(0, 1.0 - cdf_lt)
        local tail_gt = math.max(0, 1.0 - cdf_le)

        self.result_lines = {
            string.format("Media E[X] = λ = %.4g   |   Varianza V[X] = %.4g   |   Desv. σ = √λ = %.4g",
                lambda, lambda, math.sqrt(lambda)),
            string.format("Puntual P(X = %d) = %.6f   |   Intervalo P(%d ≤ X ≤ %d) = %.6f", k, pmf_k, lo, hi, p_inter),
            string.format("Acum: P(X≤%d)=%.5f | P(X<%d)=%.5f | Cola: P(X≥%d)=%.5f | P(X>%d)=%.5f",
                k, cdf_le, k, cdf_lt, k, tail_ge, k, tail_gt),
        }
    end
end

-- CÁLCULOS FINANCIEROS DEL FORMULARIO DE SARRIKO (Txulet.pdf) + VAN/TIR
function SarrikoCalc:_calcFinancial()
    local cat = self.tab
    local sub_idx = self.fin_sub[cat]
    local mode = FIN_MODES[cat][sub_idx]
    local raw = self.fin_vals[cat][sub_idx]
    local v = {}
    for k, str in pairs(raw) do
        v[k] = tonumber(str) or 0
    end

    if mode.id == "comp" then
        local C0, i, n, th = v.C0, v.i, v.n, v.theta
        local R = 1 + i
        local Rn = R ^ n
        local Vn = R ^ (-n)
        local Cn = C0 * Rn
        local I = Cn - C0
        local C0_act = C0 * Vn
        local m = math.floor(n)
        local Cn_lin = C0 * (R ^ m) * (1 + th * i)
        self.result_lines = {
            string.format("Cap. Compuesta:  Cn = %.2f €   |   Interés I = %.2f €", Cn, I),
            string.format("Actualización (si Cn=%.0f):  C0 = %.2f €   |   Desc. D = %.2f €", C0, C0_act, C0 - C0_act),
            string.format("Factores: R^n = %.6f  |  V^n = %.6f  |  Conv. Lineal (θ): %.2f €", Rn, Vn, Cn_lin),
        }
    elseif mode.id == "simp" then
        local C, i, n, g, k_fijo = v.C, v.i, v.n, v.g, v.k
        local Cn_simp = C * (1 + n * i)
        local I_simp = C * n * i
        local C0_rac = C / (1 + n * i)
        local D_rac = C - C0_rac
        local D_com = C * n * i
        local C0_com = C * (1 - n * i)
        local E_banc = C0_com - C * g
        local L_banc = E_banc - k_fijo
        self.result_lines = {
            string.format("Cap. Simple:  Cn = %.2f €  (I = %.2f €)", Cn_simp, I_simp),
            string.format("Desc. Racional:  C0 = %.2f € (Dr = %.2f)  |  Comercial: C0 = %.2f € (Dc = %.2f)", C0_rac, D_rac, C0_com, D_com),
            string.format("Efectivo Bancario:  E = %.2f €   |   Líquido L = %.2f €", E_banc, L_banc),
        }
    elseif mode.id == "equiv" then
        local i, ik, k = v.i, v.ik, math.max(1, v.k)
        if math.abs(i) < 1e-12 and math.abs(ik) > 0 then
            i = ((1 + ik) ^ k) - 1
        else
            ik = ((1 + i) ^ (1 / k)) - 1
        end
        local Jk = k * ik
        local d = i / (1 + i)
        local ik_simp = i / k
        self.result_lines = {
            string.format("Compuesta:  i anual = %.6f (%.4f%%)   |   ik = %.6f (%.4f%%)", i, i * 100, ik, ik * 100),
            string.format("Tanto Nominal:  Jk = %.6f (%.4f%%)   |   Factor i/Jk = %.6f", Jk, Jk * 100, Jk ~= 0 and (i / Jk) or 1),
            string.format("Descuento equiv. d = %.6f (%.4f%%)   |   Simple ik = %.6f", d, d * 100, ik_simp),
        }
    elseif mode.id == "venc" then
        local sum_C = v.C1 + v.C2 + v.C3
        local sum_Ct = v.C1 * v.t1 + v.C2 * v.t2 + v.C3 * v.t3
        local t_med = sum_C ~= 0 and (sum_Ct / sum_C) or 0
        self.result_lines = {
            string.format("Suma de Capitales (∑Ci) = %.2f €", sum_C),
            string.format("Vencimiento Medio (Batez besteko mugaeguna):  n = %.4f periodos", t_med),
        }
    elseif mode.id == "const" then
        local M, i, n, k = v.M, v.i, v.n, math.max(1, v.k)
        if math.abs(i) < 1e-12 then
            self.result_lines = { string.format("Sin interés (i=0):  Va = Vs = %.2f €", M * n) }
            return
        end
        local ani = (1 - ((1 + i) ^ (-n))) / i
        local sni = (((1 + i) ^ n) - 1) / i
        local ik = ((1 + i) ^ (1 / k)) - 1
        local Jk = k * ik
        local frac_corr = (k > 1 and Jk ~= 0) and (i / Jk) or 1
        local Va = M * ani * frac_corr
        local Vs = M * sni * frac_corr
        local Va_pre = Va * (1 + i)
        local Vs_pre = Vs * (1 + i)
        local perp = (M / i) * frac_corr
        self.result_lines = {
            string.format("a_n|i = %.6f   |   s_n|i = %.6f   |   Perpetua Va_∞ = %.2f €", ani, sni, perp),
            string.format("Pospagable:  Va = %.2f €   |   Vs = %.2f €", Va, Vs),
            string.format("Prepagable (ä, s̈):  Vä = %.2f €   |   Vs̈ = %.2f €", Va_pre, Vs_pre),
        }
    elseif mode.id == "arit" then
        local M1, pi_v, i, n = v.M1, v.pi, v.i, v.n
        if math.abs(i) < 1e-12 then
            self.result_lines = { _("Introduce un tanto de interés i > 0.") }
            return
        end
        local Vn = (1 + i) ^ (-n)
        local ani = (1 - Vn) / i
        local sni = (((1 + i) ^ n) - 1) / i
        local Va = (M1 + pi_v / i) * ani - (n * pi_v * Vn) / i
        local Vs = (M1 + pi_v / i) * sni - (n * pi_v) / i
        local perp = (M1 + pi_v / i) / i
        self.result_lines = {
            string.format("Pospagable:  A(M1,π) = %.2f €   |   Valor Final S(M1,π) = %.2f €", Va, Vs),
            string.format("Prepagable:  Ä = %.2f €   |   S̈ = %.2f €", Va * (1 + i), Vs * (1 + i)),
            string.format("Renta Perpetua Aritmética:  A_∞ = %.2f €", perp),
        }
    elseif mode.id == "geom" then
        local M1, q, i, n = v.M1, v.q, v.i, v.n
        local R = 1 + i
        local Vn = R ^ (-n)
        local Va, Vs
        if math.abs(R - q) < 1e-9 then
            Va = M1 * n / R
            Vs = M1 * n * (R ^ (n - 1))
        else
            Va = M1 * (1 - (q ^ n) * Vn) / (R - q)
            Vs = M1 * ((R ^ n) - (q ^ n)) / (R - q)
        end
        local perp_str = (q < R) and string.format("%.2f €", M1 / (R - q)) or "Diverge (q ≥ 1+i)"
        self.result_lines = {
            string.format("Pospagable:  A(M1,q) = %.2f €   |   Valor Final S(M1,q) = %.2f €", Va, Vs),
            string.format("Prepagable:  Ä = %.2f €   |   Perpetua A_∞ = %s", Va * R, perp_str),
        }
    elseif mode.id == "frances" then
        local P, i, n, t = v.P, v.i, math.max(1, v.n), math.max(1, math.min(v.n, v.t))
        if math.abs(i) < 1e-12 then return end
        local ani = (1 - ((1 + i) ^ (-n))) / i
        local M = P / ani
        local A1 = M - P * i
        local At = A1 * ((1 + i) ^ (t - 1))
        local It = M - At
        local an_t = (1 - ((1 + i) ^ (-(n - t)))) / i
        local Dt = M * an_t
        local Tt = P - Dt
        self.result_lines = {
            string.format("Cuota constante M = %.2f €   |   Primera amort. A1 = %.2f €", M, A1),
            string.format("Periodo t=%d:  Interés It = %.2f €   |   Amortización At = %.2f €", t, It, At),
            string.format("Capital Vivo Dt = %.2f €   |   Total Amortizado Tt = %.2f €", Dt, Tt),
        }
    elseif mode.id == "ital_amer" then
        local P, i, n, t, ifo = v.P, v.i, math.max(1, v.n), math.max(1, math.min(v.n, v.t)), v.ifondo
        local A = P / n
        local Dt_prev = (n - (t - 1)) * A
        local It_ital = Dt_prev * i
        local Mt_ital = A + It_ital
        local Dt_ital = (n - t) * A
        local sni_pre = (math.abs(ifo) > 1e-12) and ((((1 + ifo) ^ n) - 1) / ifo) * (1 + ifo) or n
        local M_fondo = P / sni_pre
        self.result_lines = {
            string.format("ITALIANO (t=%d):  A = %.2f €  |  It = %.2f €  |  Cuota Mt = %.2f €", t, A, It_ital, Mt_ital),
            string.format("ITALIANO:  Capital Vivo Dt = %.2f €  |  Amortizado Tt = %.2f €", Dt_ital, P - Dt_ital),
            string.format("AMERICANO: Interés P*i = %.2f € | Cuota Sinking = %.2f € (Total = %.2f €)", P * i, M_fondo, P * i + M_fondo),
        }
    elseif mode.id == "eraketa" then
        local C, i, n, t = v.C, v.i, math.max(1, v.n), math.max(1, math.min(v.n, v.t))
        if math.abs(i) < 1e-12 then return end
        local sni_pre = ((((1 + i) ^ n) - 1) / i) * (1 + i)
        local M = C / sni_pre
        local sti_pre = ((((1 + i) ^ t) - 1) / i) * (1 + i)
        local Ft = M * sti_pre
        local Ft_prev = (t > 1) and (M * ((((1 + i) ^ (t - 1)) - 1) / i) * (1 + i)) or 0
        local It = (Ft_prev + M) * i
        local Ct_star = M + It
        self.result_lines = {
            string.format("Cuota Constitución Prepagable M = %.2f €", M),
            string.format("En t=%d:  Fondo Acumulado Ft = %.2f €   |   Reserva Pt = %.2f €", t, Ft, C - Ft),
            string.format("Interés del periodo It = %.2f €   |   Cuota Constitución C*t = %.2f €", It, Ct_star),
        }
    elseif mode.id == "vantir" then
        local I0, k = v.I0, v.k
        local Q = { v.Q1, v.Q2, v.Q3, v.Q4 }
        local function npv(rate)
            local val = -I0
            for j = 1, 4 do
                val = val + Q[j] * ((1 + rate) ^ (-j))
            end
            return val
        end
        local van = npv(k)
        local r0, r1 = 0.05, 0.15
        local tir_ok = false
        for _ = 1, 60 do
            local f0, f1 = npv(r0), npv(r1)
            if math.abs(f1) < 1e-7 then
                tir_ok = true
                break
            end
            if math.abs(f1 - f0) < 1e-12 then break end
            local r2 = r1 - f1 * (r1 - r0) / (f1 - f0)
            if r2 < -0.95 then r2 = -0.9 end
            r0, r1 = r1, r2
        end
        local acum = 0
        local payback_str = "No recupera"
        for j = 1, 4 do
            local prev = acum
            acum = acum + Q[j]
            if acum >= I0 and Q[j] > 0 then
                local exact_pb = (j - 1) + (I0 - prev) / Q[j]
                payback_str = string.format("%.2f años", exact_pb)
                break
            end
        end
        local tir_str = tir_ok and string.format("%.4f%% (r=%.5f)", r1 * 100, r1) or "No converge"
        self.result_lines = {
            string.format("VAN (al %.2f%%) = %.2f €   (%s)", k * 100, van, van >= 0 and "VIABLE" or "NO VIABLE"),
            string.format("TIR Exacta = %s   |   Payback = %s", tir_str, payback_str),
        }
    end
end

function SarrikoCalc:_recalculate()
    if self.tab == "poly" then
        self:_calcPolynomial()
    elseif self.tab == "sys" then
        self:_calcLinearSystem()
    elseif self.tab == "stat" then
        self:_calcStatistics()
    else
        self:_calcFinancial()
    end
end

function SarrikoCalc:_buildBodySection(panel_w, sub_h, field_h)
    local rows = VerticalGroup:new({ align = "center" })

    if self.tab == "poly" then
        local w3 = math.floor((panel_w - 18) / 3)
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton(self.poly_deg == 2 and "• Grado 2 (ax²+bx+c) •" or "Grado 2", function()
                self.poly_deg = 2
                self.poly_sel = 1
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w3, sub_h, self.poly_deg == 2 and 4 or 1),
            self:_makeButton(self.poly_deg == 3 and "• Grado 3 (ax³+...) •" or "Grado 3", function()
                self.poly_deg = 3
                self.poly_sel = 1
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w3, sub_h, self.poly_deg == 3 and 4 or 1),
            self:_makeButton(self.poly_deg == 4 and "• Grado 4 (ax⁴+...) •" or "Grado 4", function()
                self.poly_deg = 4
                self.poly_sel = 1
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w3, sub_h, self.poly_deg == 4 and 4 or 1),
        }))

        local labels = {
            [2] = { "a (x²)", "b (x)", "c (indep)" },
            [3] = { "a (x³)", "b (x²)", "c (x)", "d (indep)" },
            [4] = { "a (x⁴)", "b (x³)", "c (x²)", "d (x)", "e (indep)" },
        }
        local cur_labels = labels[self.poly_deg]
        local n_c = #cur_labels
        local btn_w = math.floor((panel_w - 16) / 2)

        for i = 1, n_c, 2 do
            local line = HorizontalGroup:new({ align = "center" })
            for j = i, math.min(i + 1, n_c) do
                local is_sel = (self.poly_sel == j)
                local txt = string.format("%s%s = %s", is_sel and "▶ " or "", cur_labels[j], self.poly_coeffs[j])
                table.insert(line, self:_makeButton(txt, function()
                    self.poly_sel = j
                    self.fresh_field = true
                    self:show()
                end, btn_w, field_h, is_sel and 4 or 2))
            end
            table.insert(rows, line)
        end

    elseif self.tab == "sys" then
        local w5 = math.floor((panel_w - 24) / 5)
        local size_row = HorizontalGroup:new({ align = "center" })
        local size_labels = {
            [2] = "2×2 (x,y)",
            [3] = "3×3 (..z)",
            [4] = "4×4 (..a)",
            [5] = "5×5 (..b)",
            [6] = "6×6 (..c)",
        }
        for sz = 2, 6 do
            local active = (self.sys_n == sz)
            table.insert(size_row, self:_makeButton(active and ("•" .. size_labels[sz] .. "•") or size_labels[sz], function()
                self.sys_n = sz
                self.sys_eq = 1
                self.sys_col = 1
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w5, sub_h, active and 4 or 1))
        end
        table.insert(rows, size_row)

        local nav_w = math.floor((panel_w - 18) / 3)
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton("◀ Ecuación Ant.", function()
                self.sys_eq = ((self.sys_eq - 2) % self.sys_n) + 1
                self.fresh_field = true
                self:show()
            end, nav_w, sub_h, 2),
            self:_makeText(string.format("Editando Ecuación %d de %d", self.sys_eq, self.sys_n), 17),
            self:_makeButton("Ecuación Sig. ▶", function()
                self.sys_eq = (self.sys_eq % self.sys_n) + 1
                self.fresh_field = true
                self:show()
            end, nav_w, sub_h, 2),
        }))

        local n_cols = self.sys_n + 1
        local col_w = math.floor((panel_w - 20) / math.min(4, n_cols))
        local coeff_row1 = HorizontalGroup:new({ align = "center" })
        local coeff_row2 = HorizontalGroup:new({ align = "center" })

        for c = 1, n_cols do
            local is_sel = (self.sys_col == c)
            local v_name = (c <= self.sys_n) and VAR_NAMES[c] or "="
            local val_str = (c <= self.sys_n) and self.sys_mat[self.sys_eq][c] or self.sys_mat[self.sys_eq][7]
            local label = (c <= self.sys_n)
                and string.format("%s%s:%s", is_sel and "▶" or "", val_str, v_name)
                or string.format("%s= %s", is_sel and "▶" or "", val_str)

            local btn = self:_makeButton(label, function()
                self.sys_col = c
                self.fresh_field = true
                self:show()
            end, col_w, field_h, is_sel and 4 or 2)

            if c <= 4 then
                table.insert(coeff_row1, btn)
            else
                table.insert(coeff_row2, btn)
            end
        end
        table.insert(rows, coeff_row1)
        if n_cols > 4 then
            table.insert(rows, coeff_row2)
        end

        for r = 1, self.sys_n do
            local parts = {}
            for c = 1, self.sys_n do
                local v = self.sys_mat[r][c]
                table.insert(parts, v .. VAR_NAMES[c])
            end
            local eq_str = string.format(
                "%sEc.%d:  %s = %s",
                r == self.sys_eq and "▶ " or "   ",
                r,
                table.concat(parts, " + "),
                self.sys_mat[r][7]
            )
            table.insert(rows, self:_makeText(eq_str, 14))
        end

    elseif self.tab == "stat" then
        local w5 = math.floor((panel_w - 24) / 5)
        local sub_labels = { "1-Var (x,n)", "2-Var Reg", "Normal", "Binomial", "Poisson" }
        local sub_row = HorizontalGroup:new({ align = "center" })
        for s_idx, s_name in ipairs(sub_labels) do
            local active = (self.stat_sub == s_idx)
            table.insert(sub_row, self:_makeButton(active and ("•" .. s_name .. "•") or s_name, function()
                self.stat_sub = s_idx
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w5, sub_h, active and 4 or 1))
        end
        table.insert(rows, sub_row)

        if self.stat_sub == 1 then
            local w3 = math.floor((panel_w - 18) / 3)
            table.insert(rows, HorizontalGroup:new({
                align = "center",
                self:_makeButton(string.format("Nº Datos: %d (+1)", self.stat1_n), function()
                    self.stat1_n = (self.stat1_n % 7) + 2 -- Cicla de 2 a 8 datos
                    if self.stat1_sel > self.stat1_n then self.stat1_sel = 1 end
                    self.fresh_field = true
                    self:_recalculate()
                    self:show()
                end, w3, sub_h, 2),
                self:_makeButton(self.stat1_mode == "x" and "• Editando xi •" or "Editar xi", function()
                    self.stat1_mode = "x"
                    self.fresh_field = true
                    self:show()
                end, w3, sub_h, self.stat1_mode == "x" and 4 or 1),
                self:_makeButton(self.stat1_mode == "f" and "• Editando frec ni •" or "Editar frec ni", function()
                    self.stat1_mode = "f"
                    self.fresh_field = true
                    self:show()
                end, w3, sub_h, self.stat1_mode == "f" and 4 or 1),
            }))

            local btn_w = math.floor((panel_w - 20) / 4)
            local r1 = HorizontalGroup:new({ align = "center" })
            local r2 = HorizontalGroup:new({ align = "center" })
            for i = 1, self.stat1_n do
                local is_sel = (self.stat1_sel == i)
                local lbl = string.format(
                    "%sx%d=%s (n=%s)",
                    is_sel and "▶" or "",
                    i,
                    self.stat1_x[i],
                    self.stat1_f[i]
                )
                local b = self:_makeButton(lbl, function()
                    self.stat1_sel = i
                    self.fresh_field = true
                    self:show()
                end, btn_w, field_h, is_sel and 4 or 2)
                if i <= 4 then
                    table.insert(r1, b)
                else
                    table.insert(r2, b)
                end
            end
            table.insert(rows, r1)
            if self.stat1_n > 4 then
                table.insert(rows, r2)
            end

        elseif self.stat_sub == 2 then
            local w4 = math.floor((panel_w - 20) / 4)
            table.insert(rows, HorizontalGroup:new({
                align = "center",
                self:_makeButton(string.format("Pares: %d (+1)", self.stat2_n), function()
                    self.stat2_n = (self.stat2_n - 1) % 5 + 2 -- Cicla de 2 a 6 pares
                    if self.stat2_sel > self.stat2_n then self.stat2_sel = 1 end
                    self.fresh_field = true
                    self:_recalculate()
                    self:show()
                end, w4, sub_h, 2),
                self:_makeButton(self.stat2_mode == "x" and "• Edit X •" or "Edit X", function()
                    self.stat2_mode = "x"
                    self.fresh_field = true
                    self:show()
                end, w4, sub_h, self.stat2_mode == "x" and 4 or 1),
                self:_makeButton(self.stat2_mode == "y" and "• Edit Y •" or "Edit Y", function()
                    self.stat2_mode = "y"
                    self.fresh_field = true
                    self:show()
                end, w4, sub_h, self.stat2_mode == "y" and 4 or 1),
                self:_makeButton(self.stat2_mode == "x0" and ("▶ x0=" .. self.stat2_x0) or ("x0=" .. self.stat2_x0), function()
                    self.stat2_mode = "x0"
                    self.fresh_field = true
                    self:show()
                end, w4, sub_h, self.stat2_mode == "x0" and 4 or 1),
            }))

            local btn_w = math.floor((panel_w - 18) / 3)
            local r1 = HorizontalGroup:new({ align = "center" })
            local r2 = HorizontalGroup:new({ align = "center" })
            for i = 1, self.stat2_n do
                local is_sel = (self.stat2_mode ~= "x0") and (self.stat2_sel == i)
                local lbl = string.format(
                    "%s(%s ; %s)",
                    is_sel and "▶" or "",
                    self.stat2_x[i],
                    self.stat2_y[i]
                )
                local b = self:_makeButton(lbl, function()
                    if self.stat2_mode == "x0" then self.stat2_mode = "x" end
                    self.stat2_sel = i
                    self.fresh_field = true
                    self:show()
                end, btn_w, field_h, is_sel and 4 or 2)
                if i <= 3 then
                    table.insert(r1, b)
                else
                    table.insert(r2, b)
                end
            end
            table.insert(rows, r1)
            if self.stat2_n > 3 then
                table.insert(rows, r2)
            end

        else
            local d_def = DIST_MODES[self.stat_sub]
            local vals = self.dist_vals[self.stat_sub]
            local f_list = d_def.fields
            local btn_w = math.floor((panel_w - 16) / 2)

            for i = 1, #f_list, 2 do
                local line = HorizontalGroup:new({ align = "center" })
                for j = i, math.min(i + 1, #f_list) do
                    local f = f_list[j]
                    local is_sel = (self.dist_sel == j)
                    local txt = string.format("%s%s: %s", is_sel and "▶ " or "", f.label, vals[f.k])
                    table.insert(line, self:_makeButton(txt, function()
                        self.dist_sel = j
                        self.fresh_field = true
                        self:show()
                    end, btn_w, field_h, is_sel and 4 or 2))
                end
                table.insert(rows, line)
            end
        end

    else
        -- Pestañas Financieras
        local list = FIN_MODES[self.tab]
        local sub_idx = self.fin_sub[self.tab]
        local w_sub = math.floor((panel_w - 20) / #list)
        local sub_row = HorizontalGroup:new({ align = "center" })

        for idx, m in ipairs(list) do
            local active = (idx == sub_idx)
            table.insert(sub_row, self:_makeButton(active and ("•" .. m.name .. "•") or m.name, function()
                self.fin_sub[self.tab] = idx
                self.fin_sel = 1
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w_sub, sub_h, active and 4 or 1))
        end
        table.insert(rows, sub_row)

        local mode_def = list[sub_idx]
        local vals = self.fin_vals[self.tab][sub_idx]
        local f_list = mode_def.fields
        local btn_w = math.floor((panel_w - 16) / 2)

        for i = 1, #f_list, 2 do
            local line = HorizontalGroup:new({ align = "center" })
            for j = i, math.min(i + 1, #f_list) do
                local f = f_list[j]
                local is_sel = (self.fin_sel == j)
                local txt = string.format("%s%s: %s", is_sel and "▶ " or "", f.label, vals[f.k])
                table.insert(line, self:_makeButton(txt, function()
                    self.fin_sel = j
                    self.fresh_field = true
                    self:show()
                end, btn_w, field_h, is_sel and 4 or 2))
            end
            table.insert(rows, line)
        end
    end

    return rows
end

function SarrikoCalc:_getCurrentFormulaBanner()
    if self.tab == "poly" then
        if self.poly_deg == 2 then
            return "Fórmula:  a·x² + b·x + c = 0   →   x = (-b ± √(b² - 4ac)) / 2a"
        elseif self.poly_deg == 3 then
            return "Fórmula Cardano:  a·x³ + b·x² + c·x + d = 0"
        else
            return "Fórmula Ferrari:  a·x⁴ + b·x³ + c·x² + d·x + e = 0"
        end
    elseif self.tab == "sys" then
        return "Sistema Lineal A·X = B  (Variables: x, y, z, a, b, c) — Gauss con Pivoteo"
    elseif self.tab == "stat" then
        if self.stat_sub == 1 then
            return "1-Var:  x̄ = (∑xi·ni)/N  |  σ² = (∑xi²·ni)/N - x̄²  |  S² = σ²·N/(N-1)  |  CV = σ/|x̄|"
        elseif self.stat_sub == 2 then
            return "2-Var:  σxy = (∑xi·yi)/N - x̄·ȳ  |  r = σxy/(σx·σy)  |  Recta Y/X: b = σxy/σx², a = ȳ - b·x̄"
        else
            return DIST_MODES[self.stat_sub].formula
        end
    else
        local sub_idx = self.fin_sub[self.tab]
        return FIN_MODES[self.tab][sub_idx].formula
    end
end

function SarrikoCalc:show()
    self:_closeWindow(false)

    local screen_w = Screen:getWidth()
    local screen_h = Screen:getHeight()
    local panel_w = screen_w - 16

    local top_h = math.max(36, math.floor(screen_h * 0.052))
    local sub_h = math.max(34, math.floor(screen_h * 0.048))
    local field_h = math.max(38, math.floor(screen_h * 0.055))
    local key_h = math.max(42, math.floor(screen_h * 0.068))

    local w6 = math.floor((panel_w - 26) / 6)
    local w5 = math.floor((panel_w - 24) / 5)

    local header_row = HorizontalGroup:new({
        align = "center",
        self:_makeText(_("SARRIKO FINANTZA, ALGEBRA & ESTADÍSTICA"), 16),
        self:_makeButton(self.show_formula and _("Fórmula: SÍ") or _("Fórmula: NO"), function()
            self.show_formula = not self.show_formula
            self:show()
        end, math.floor(panel_w * 0.22), top_h, 2),
        self:_makeButton(_("Salir"), function()
            self:_closeWindow(true)
        end, math.floor(panel_w * 0.16), top_h, 2),
    })

    local tabs = {
        { id = "poly", label = "Polinom" },
        { id = "sys", label = "Sist.N×N" },
        { id = "cap", label = "Kapitala" },
        { id = "rent", label = "Errentak" },
        { id = "loan", label = "Mailegu" },
        { id = "stat", label = "Estadíst." },
    }
    local tab_row = HorizontalGroup:new({ align = "center" })
    for _, t in ipairs(tabs) do
        local active = (self.tab == t.id)
        table.insert(tab_row, self:_makeButton(active and ("•" .. t.label .. "•") or t.label, function()
            self.tab = t.id
            self.fresh_field = true
            self:_recalculate()
            self:show()
        end, w6, top_h, active and 4 or 1))
    end

    local body_section = self:_buildBodySection(panel_w, sub_h, field_h)

    local res_group = VerticalGroup:new({ align = "left" })
    if self.show_formula then
        table.insert(res_group, self:_makeText(self:_getCurrentFormulaBanner(), 13))
    end
    for _, line in ipairs(self.result_lines) do
        table.insert(res_group, self:_makeText("• " .. line, 15))
    end

    local result_box = FrameContainer:new({
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 3,
        padding = 6,
        margin = 3,
        CenterContainer:new({
            dimen = Geom:new({ w = panel_w - 16, h = math.floor(screen_h * 0.17) }),
            res_group,
        }),
    })

    local k_row1 = HorizontalGroup:new({
        align = "center",
        self:_makeButton("7", function() self:_onKeyPress("7") end, w5, key_h, 2),
        self:_makeButton("8", function() self:_onKeyPress("8") end, w5, key_h, 2),
        self:_makeButton("9", function() self:_onKeyPress("9") end, w5, key_h, 2),
        self:_makeButton("+/-", function() self:_onKeyPress("+/-") end, w5, key_h, 2),
        self:_makeButton("DEL", function() self:_onKeyPress("DEL") end, w5, key_h, 3),
    })

    local k_row2 = HorizontalGroup:new({
        align = "center",
        self:_makeButton("4", function() self:_onKeyPress("4") end, w5, key_h, 2),
        self:_makeButton("5", function() self:_onKeyPress("5") end, w5, key_h, 2),
        self:_makeButton("6", function() self:_onKeyPress("6") end, w5, key_h, 2),
        self:_makeButton(".", function() self:_onKeyPress(".") end, w5, key_h, 2),
        self:_makeButton("C (0)", function() self:_onKeyPress("CLR") end, w5, key_h, 3),
    })

    local k_row3 = HorizontalGroup:new({
        align = "center",
        self:_makeButton("1", function() self:_onKeyPress("1") end, w5, key_h, 2),
        self:_makeButton("2", function() self:_onKeyPress("2") end, w5, key_h, 2),
        self:_makeButton("3", function() self:_onKeyPress("3") end, w5, key_h, 2),
        self:_makeButton("0", function() self:_onKeyPress("0") end, w5, key_h, 2),
        self:_makeButton("Sig. ▶", function() self:_onKeyPress("NEXT") end, w5, key_h, 3),
    })

    local layout = VerticalGroup:new({
        align = "center",
        header_row,
        tab_row,
        body_section,
        result_box,
        k_row1,
        k_row2,
        k_row3,
    })

    self.window = FrameContainer:new({
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 0,
        padding = 0,
        margin = 0,
        CenterContainer:new({
            dimen = Screen:getSize(),
            layout,
        }),
    })

    UIManager:show(self.window)
    UIManager:setDirty(self.window, "ui")
    UIManager:setDirty("all", "ui")
end

return SarrikoCalc