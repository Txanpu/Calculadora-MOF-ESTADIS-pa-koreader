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
local SQRT_2PI = math.sqrt(2 * math.pi)

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

-- Funciones de distribución de probabilidad
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
    return (sign == 1) and cdf_pos or (1.0 - cdf_pos)
end

local function norm_inv(p)
    if p <= 0 or p >= 1 then return 0 end
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
        if d > 1e-14 then z = z - err / d end
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
    local x = n + 1
    return (x - 0.5) * math.log(x) - x + 0.5 * math.log(2 * math.pi) + 1.0 / (12.0 * x) - 1.0 / (360.0 * x * x * x)
end

local function binom_pmf(n, k, p)
    if k < 0 or k > n then return 0 end
    if p <= 0 then return (k == 0) and 1 or 0 end
    if p >= 1 then return (k == n) and 1 or 0 end
    local ln_comb = log_fact(n) - log_fact(k) - log_fact(n - k)
    return math.exp(ln_comb + k * math.log(p) + (n - k) * math.log(1 - p))
end

local function pois_pmf(lambda, k)
    if k < 0 or lambda <= 0 then return (k == 0 and lambda == 0) and 1 or 0 end
    return math.exp(-lambda + k * math.log(lambda) - log_fact(k))
end

-- ============================================================================
-- MOTOR SIMBÓLICO DE CÁLCULO (AST: DERIVADAS E INTEGRALES SIMBÓLICAS Y DEFINIDAS)
-- ============================================================================
local function n_num(v) return { op = "num", val = v } end
local function n_var() return { op = "var" } end
local function n_bin(op, l, r) return { op = op, l = l, r = r } end
local function n_un(op, a) return { op = op, arg = a } end
local function n_fn(name, a) return { op = "fn", name = name, arg = a } end

local function is_num(node, val)
    if not node or node.op ~= "num" then return false end
    if val == nil then return true end
    return math.abs(node.val - val) < 1e-11
end

local function has_var(node)
    if not node then return false end
    if node.op == "var" then return true end
    if node.op == "num" then return false end
    if node.op == "neg" or node.op == "fn" then return has_var(node.arg) end
    return has_var(node.l) or has_var(node.r)
end

local function ast_clone(node)
    if not node then return nil end
    if node.op == "num" then return n_num(node.val) end
    if node.op == "var" then return n_var() end
    if node.op == "neg" then return n_un("neg", ast_clone(node.arg)) end
    if node.op == "fn" then return n_fn(node.name, ast_clone(node.arg)) end
    return n_bin(node.op, ast_clone(node.l), ast_clone(node.r))
end

local function ast_equal(a, b)
    if not a or not b or a.op ~= b.op then return false end
    if a.op == "num" then return math.abs(a.val - b.val) < 1e-9 end
    if a.op == "var" then return true end
    if a.op == "neg" then return ast_equal(a.arg, b.arg) end
    if a.op == "fn" then return a.name == b.name and ast_equal(a.arg, b.arg) end
    return ast_equal(a.l, b.l) and ast_equal(a.r, b.r)
end

local function ast_eval(node, x_val)
    if not node then return 0 end
    if node.op == "num" then return node.val end
    if node.op == "var" then return x_val end
    if node.op == "neg" then return -ast_eval(node.arg, x_val) end
    if node.op == "+" then return ast_eval(node.l, x_val) + ast_eval(node.r, x_val) end
    if node.op == "-" then return ast_eval(node.l, x_val) - ast_eval(node.r, x_val) end
    if node.op == "*" then return ast_eval(node.l, x_val) * ast_eval(node.r, x_val) end
    if node.op == "/" then return ast_eval(node.l, x_val) / ast_eval(node.r, x_val) end
    if node.op == "^" then return ast_eval(node.l, x_val) ^ ast_eval(node.r, x_val) end
    if node.op == "fn" then
        local v = ast_eval(node.arg, x_val)
        local fn = node.name
        if fn == "sin" then return math.sin(v)
        elseif fn == "cos" then return math.cos(v)
        elseif fn == "tan" then return math.tan(v)
        elseif fn == "ln" then return math.log(v)
        elseif fn == "log" then return math.log(v) / math.log(10)
        elseif fn == "exp" then return math.exp(v)
        elseif fn == "sqrt" then return math.sqrt(v)
        elseif fn == "asin" then return math.asin(v)
        elseif fn == "acos" then return math.acos(v)
        elseif fn == "atan" then return math.atan(v)
        end
    end
    return 0
end

local function ast_simplify(node)
    if not node then return n_num(0) end
    if node.op == "num" or node.op == "var" then
        if node.op == "num" and math.abs(node.val) < 1e-12 then node.val = 0 end
        return node
    end
    if node.op == "neg" then
        local a = ast_simplify(node.arg)
        if is_num(a) then return n_num(-a.val) end
        if a.op == "neg" then return a.arg end
        return n_un("neg", a)
    end
    if node.op == "fn" then
        local a = ast_simplify(node.arg)
        if is_num(a) and not has_var(a) then
            local v = ast_eval(n_fn(node.name, a), 0)
            if v == v and math.abs(v) ~= math.huge then return n_num(v) end
        end
        return n_fn(node.name, a)
    end

    local l = ast_simplify(node.l)
    local r = ast_simplify(node.r)
    local op = node.op

    if is_num(l) and is_num(r) then
        local v = ast_eval(n_bin(op, l, r), 0)
        if v == v and math.abs(v) ~= math.huge then return n_num(v) end
    end

    if op == "+" then
        if is_num(l, 0) then return r end
        if is_num(r, 0) then return l end
        if r.op == "neg" then return ast_simplify(n_bin("-", l, r.arg)) end
        if is_num(r) and r.val < 0 then return ast_simplify(n_bin("-", l, n_num(-r.val))) end
        if ast_equal(l, r) then return ast_simplify(n_bin("*", n_num(2), l)) end
    elseif op == "-" then
        if is_num(r, 0) then return l end
        if is_num(l, 0) then return ast_simplify(n_un("neg", r)) end
        if r.op == "neg" then return ast_simplify(n_bin("+", l, r.arg)) end
        if is_num(r) and r.val < 0 then return ast_simplify(n_bin("+", l, n_num(-r.val))) end
        if ast_equal(l, r) then return n_num(0) end
    elseif op == "*" then
        if is_num(l, 0) or is_num(r, 0) then return n_num(0) end
        if is_num(l, 1) then return r end
        if is_num(r, 1) then return l end
        if is_num(l, -1) then return ast_simplify(n_un("neg", r)) end
        if is_num(r, -1) then return ast_simplify(n_un("neg", l)) end
        -- Poner constante siempre a la izquierda
        if is_num(r) and not is_num(l) then l, r = r, l end
        -- Asociatividad de constantes: c1 * (c2 * u) -> (c1*c2) * u
        if is_num(l) and r.op == "*" and is_num(r.l) then
            return ast_simplify(n_bin("*", n_num(l.val * r.l.val), r.r))
        end
        -- x * x -> x^2 y x * x^n -> x^(n+1)
        if ast_equal(l, r) then
            return ast_simplify(n_bin("^", l, n_num(2)))
        end
        if l.op == "^" and ast_equal(l.l, r) and is_num(l.r) then
            return ast_simplify(n_bin("^", r, n_num(l.r.val + 1)))
        end
        if r.op == "^" and ast_equal(r.l, l) and is_num(r.r) then
            return ast_simplify(n_bin("^", l, n_num(r.r.val + 1)))
        end
    elseif op == "/" then
        if is_num(l, 0) then return n_num(0) end
        if is_num(r, 1) then return l end
        if ast_equal(l, r) then return n_num(1) end
    elseif op == "^" then
        if is_num(r, 0) then return n_num(1) end
        if is_num(r, 1) then return l end
        if is_num(l, 0) then return n_num(0) end
        if is_num(l, 1) then return n_num(1) end
        if l.op == "^" and is_num(l.r) and is_num(r) then
            return ast_simplify(n_bin("^", l.l, n_num(l.r.val * r.val)))
        end
    end

    return n_bin(op, l, r)
end

-- Formateador algebraico limpio de AST a texto matemático
local OP_PREC = { ["+"] = 1, ["-"] = 1, ["*"] = 2, ["/"] = 2, ["neg"] = 3, ["^"] = 4 }

local function ast_tostring(node, parent_prec, is_right)
    if not node then return "0" end
    parent_prec = parent_prec or 0
    if node.op == "num" then
        local v = node.val
        if math.abs(v - math.pi) < 1e-9 then return "π" end
        if math.abs(v - math.exp(1)) < 1e-9 then return "e" end
        if math.abs(v - math.floor(v + 0.5)) < 1e-9 then
            return tostring(math.floor(v + 0.5))
        end
        return string.format("%.4g", v)
    elseif node.op == "var" then
        return "x"
    elseif node.op == "neg" then
        local inner = ast_tostring(node.arg, 3, false)
        local s = "-" .. inner
        return (parent_prec > 3) and ("(" .. s .. ")") or s
    elseif node.op == "fn" then
        if node.name == "exp" then
            return "e^(" .. ast_tostring(node.arg, 0, false) .. ")"
        elseif node.name == "sqrt" then
            return "√(" .. ast_tostring(node.arg, 0, false) .. ")"
        end
        return node.name .. "(" .. ast_tostring(node.arg, 0, false) .. ")"
    end

    local prec = OP_PREC[node.op] or 1
    local ls = ast_tostring(node.l, prec, false)
    local rs = ast_tostring(node.r, prec, true)

    local res
    if node.op == "*" then
        -- Multiplicación limpia: 3*x -> 3x, 2*sin(x) -> 2·sin(x)
        if is_num(node.l) and (node.r.op == "var" or (node.r.op == "^" and node.r.l.op == "var")) then
            res = ls .. rs
        else
            res = ls .. "·" .. rs
        end
    elseif node.op == "+" or node.op == "-" then
        res = ls .. " " .. node.op .. " " .. rs
    else
        res = ls .. node.op .. rs
    end

    local need_parens = (prec < parent_prec)
        or (prec == parent_prec and is_right and (node.op == "-" or node.op == "/"))
    return need_parens and ("(" .. res .. ")") or res
end

-- Tokenizador y Parser recursivo descendente con multiplicación implícita
local function parse_expr(str)
    local s = string.gsub(str or "", "%s+", "")
    s = string.gsub(s, "·", "*")
    s = string.gsub(s, "×", "*")
    s = string.gsub(s, "÷", "/")
    s = string.gsub(s, "−", "-")
    s = string.gsub(s, "π", "pi")
    s = string.gsub(s, "√%(", "sqrt(")

    local tokens = {}
    local i = 1
    local len = #s
    while i <= len do
        local ch = string.sub(s, i, i)
        if string.match(ch, "%d") or ch == "." then
            local j = i
            while j <= len and string.match(string.sub(s, j, j), "[%d%.]") do j = j + 1 end
            local num_v = tonumber(string.sub(s, i, j - 1))
            if not num_v then return nil end
            table.insert(tokens, { t = "num", v = num_v })
            i = j
        elseif string.match(ch, "%a") then
            local j = i
            while j <= len and string.match(string.sub(s, j, j), "%a") do j = j + 1 end
            local word = string.lower(string.sub(s, i, j - 1))
            if word == "x" then
                table.insert(tokens, { t = "var" })
            elseif word == "pi" then
                table.insert(tokens, { t = "num", v = math.pi })
            elseif word == "e" then
                table.insert(tokens, { t = "num", v = math.exp(1) })
            elseif word == "sen" then
                table.insert(tokens, { t = "fn", v = "sin" })
            else
                table.insert(tokens, { t = "fn", v = word })
            end
            i = j
        elseif ch == "+" or ch == "-" or ch == "*" or ch == "/" or ch == "^" or ch == "(" or ch == ")" then
            table.insert(tokens, { t = ch })
            i = i + 1
        else
            i = i + 1
        end
    end

    -- Inserción automática de '*' en multiplicación implícita: 3x, 2(x+1), x(x+1), 4sin(x)
    local clean = {}
    for idx, tk in ipairs(tokens) do
        table.insert(clean, tk)
        local nxt = tokens[idx + 1]
        if nxt then
            local left_val = (tk.t == "num" or tk.t == "var" or tk.t == ")")
            local right_val = (nxt.t == "var" or nxt.t == "fn" or nxt.t == "(" or (tk.t == ")" and nxt.t == "num"))
            if left_val and right_val then
                table.insert(clean, { t = "*" })
            end
        end
    end

    local pos = 1
    local parse_add, parse_mul, parse_pow, parse_unary, parse_atom

    parse_atom = function()
        local tk = clean[pos]
        if not tk then return n_num(0) end
        if tk.t == "num" then
            pos = pos + 1
            return n_num(tk.v)
        elseif tk.t == "var" then
            pos = pos + 1
            return n_var()
        elseif tk.t == "fn" then
            pos = pos + 1
            if clean[pos] and clean[pos].t == "(" then
                pos = pos + 1
                local arg = parse_add()
                if clean[pos] and clean[pos].t == ")" then pos = pos + 1 end
                return n_fn(tk.v, arg)
            else
                local arg = parse_unary()
                return n_fn(tk.v, arg)
            end
        elseif tk.t == "(" then
            pos = pos + 1
            local inner = parse_add()
            if clean[pos] and clean[pos].t == ")" then pos = pos + 1 end
            return inner
        end
        pos = pos + 1
        return n_num(0)
    end

    parse_pow = function()
        local left = parse_atom()
        if clean[pos] and clean[pos].t == "^" then
            pos = pos + 1
            local right = parse_unary()
            return n_bin("^", left, right)
        end
        return left
    end

    parse_unary = function()
        if clean[pos] and clean[pos].t == "-" then
            pos = pos + 1
            return n_un("neg", parse_unary())
        elseif clean[pos] and clean[pos].t == "+" then
            pos = pos + 1
            return parse_unary()
        end
        return parse_pow()
    end

    parse_mul = function()
        local left = parse_unary()
        while clean[pos] and (clean[pos].t == "*" or clean[pos].t == "/") do
            local op = clean[pos].t
            pos = pos + 1
            local right = parse_unary()
            left = n_bin(op, left, right)
        end
        return left
    end

    parse_add = function()
        local left = parse_mul()
        while clean[pos] and (clean[pos].t == "+" or clean[pos].t == "-") do
            local op = clean[pos].t
            pos = pos + 1
            local right = parse_mul()
            left = n_bin(op, left, right)
        end
        return left
    end

    if #clean == 0 then return nil end
    local ok, tree = pcall(parse_add)
    if not ok or not tree then return nil end
    return ast_simplify(tree)
end

-- DERIVADOR SIMBÓLICO RECURSIVO
local function ast_diff(node)
    if not node then return n_num(0) end
    if node.op == "num" then return n_num(0) end
    if node.op == "var" then return n_num(1) end
    if node.op == "neg" then return n_un("neg", ast_diff(node.arg)) end
    if node.op == "+" or node.op == "-" then
        return n_bin(node.op, ast_diff(node.l), ast_diff(node.r))
    end
    if node.op == "*" then
        -- (u*v)' = u'*v + u*v'
        return n_bin("+",
            n_bin("*", ast_diff(node.l), ast_clone(node.r)),
            n_bin("*", ast_clone(node.l), ast_diff(node.r))
        )
    end
    if node.op == "/" then
        -- (u/v)' = (u'*v - u*v') / v^2
        if not has_var(node.r) then
            return n_bin("/", ast_diff(node.l), ast_clone(node.r))
        end
        local num = n_bin("-",
            n_bin("*", ast_diff(node.l), ast_clone(node.r)),
            n_bin("*", ast_clone(node.l), ast_diff(node.r))
        )
        local den = n_bin("^", ast_clone(node.r), n_num(2))
        return n_bin("/", num, den)
    end
    if node.op == "^" then
        local u, v = node.l, node.r
        local u_var, v_var = has_var(u), has_var(v)
        if not u_var and not v_var then
            return n_num(0)
        elseif u_var and not v_var then
            -- (u^c)' = c * u^(c-1) * u'
            local c_minus_1 = ast_simplify(n_bin("-", ast_clone(v), n_num(1)))
            return n_bin("*",
                n_bin("*", ast_clone(v), n_bin("^", ast_clone(u), c_minus_1)),
                ast_diff(u)
            )
        elseif not u_var and v_var then
            -- (c^v)' = c^v * ln(c) * v'
            local ln_c = (is_num(u, math.exp(1))) and n_num(1) or n_fn("ln", ast_clone(u))
            return n_bin("*", n_bin("*", ast_clone(node), ln_c), ast_diff(v))
        else
            -- (u^v)' = u^v * (v'*ln(u) + v*u'/u)
            local term1 = n_bin("*", ast_diff(v), n_fn("ln", ast_clone(u)))
            local term2 = n_bin("/", n_bin("*", ast_clone(v), ast_diff(u)), ast_clone(u))
            return n_bin("*", ast_clone(node), n_bin("+", term1, term2))
        end
    end
    if node.op == "fn" then
        local u = node.arg
        local du = ast_diff(u)
        local fn = node.name
        if fn == "sin" then
            return n_bin("*", n_fn("cos", ast_clone(u)), du)
        elseif fn == "cos" then
            return n_un("neg", n_bin("*", n_fn("sin", ast_clone(u)), du))
        elseif fn == "tan" then
            return n_bin("/", du, n_bin("^", n_fn("cos", ast_clone(u)), n_num(2)))
        elseif fn == "ln" then
            return n_bin("/", du, ast_clone(u))
        elseif fn == "log" then
            return n_bin("/", du, n_bin("*", ast_clone(u), n_num(math.log(10))))
        elseif fn == "exp" then
            return n_bin("*", n_fn("exp", ast_clone(u)), du)
        elseif fn == "sqrt" then
            return n_bin("/", du, n_bin("*", n_num(2), n_fn("sqrt", ast_clone(u))))
        elseif fn == "asin" then
            return n_bin("/", du, n_fn("sqrt", n_bin("-", n_num(1), n_bin("^", ast_clone(u), n_num(2)))))
        elseif fn == "acos" then
            return n_un("neg", n_bin("/", du, n_fn("sqrt", n_bin("-", n_num(1), n_bin("^", ast_clone(u), n_num(2))))))
        elseif fn == "atan" then
            return n_bin("/", du, n_bin("+", n_num(1), n_bin("^", ast_clone(u), n_num(2))))
        end
    end
    return n_num(0)
end

-- Detector de expresión lineal a*x + b para sustitución directa en integrales
local function match_linear(node)
    if not node then return nil, nil end
    if not has_var(node) then
        return 0, ast_eval(node, 0)
    end
    if node.op == "var" then
        return 1, 0
    elseif node.op == "neg" then
        local a, b = match_linear(node.arg)
        if a then return -a, -b end
    elseif node.op == "*" then
        if is_num(node.l) and node.r.op == "var" then return node.l.val, 0 end
        if is_num(node.r) and node.l.op == "var" then return node.r.val, 0 end
    elseif node.op == "+" or node.op == "-" then
        local a1, b1 = match_linear(node.l)
        local a2, b2 = match_linear(node.r)
        if a1 and a2 then
            return (node.op == "+") and (a1 + a2) or (a1 - a2),
                   (node.op == "+") and (b1 + b2) or (b1 - b2)
        end
    end
    return nil, nil
end

-- INTEGRADOR SIMBÓLICO RECURSIVO
local function ast_integrate(node)
    if not node then return nil end
    if not has_var(node) then
        return ast_simplify(n_bin("*", ast_clone(node), n_var()))
    end
    if node.op == "var" then
        return n_bin("/", n_bin("^", n_var(), n_num(2)), n_num(2))
    end
    if node.op == "neg" then
        local int_a = ast_integrate(node.arg)
        if int_a then return ast_simplify(n_un("neg", int_a)) end
        return nil
    end
    if node.op == "+" or node.op == "-" then
        local il = ast_integrate(node.l)
        local ir = ast_integrate(node.r)
        if il and ir then return ast_simplify(n_bin(node.op, il, ir)) end
        return nil
    end
    if node.op == "*" then
        if not has_var(node.l) then
            local ir = ast_integrate(node.r)
            if ir then return ast_simplify(n_bin("*", ast_clone(node.l), ir)) end
        elseif not has_var(node.r) then
            local il = ast_integrate(node.l)
            if il then return ast_simplify(n_bin("*", ast_clone(node.r), il)) end
        end
        -- Integración por partes para x * exp(a*x), x * sin(a*x), x * cos(a*x), x * ln(x)
        local v_part, fn_part
        if node.l.op == "var" then v_part, fn_part = node.l, node.r
        elseif node.r.op == "var" then v_part, fn_part = node.r, node.l end
        if v_part and fn_part and fn_part.op == "fn" then
            local a, b = match_linear(fn_part.arg)
            if a and math.abs(a) > 1e-11 then
                local u_node = ast_clone(fn_part.arg)
                if fn_part.name == "exp" then
                    -- ∫ x*e^(ax+b) dx = e^(ax+b)*(a*x - 1)/a^2
                    return ast_simplify(n_bin("/",
                        n_bin("*", n_fn("exp", u_node), n_bin("-", n_bin("*", n_num(a), n_var()), n_num(1))),
                        n_num(a * a)
                    ))
                elseif fn_part.name == "sin" then
                    -- ∫ x*sin(ax+b) dx = sin(ax+b)/a^2 - x*cos(ax+b)/a
                    return ast_simplify(n_bin("-",
                        n_bin("/", n_fn("sin", ast_clone(u_node)), n_num(a * a)),
                        n_bin("/", n_bin("*", n_var(), n_fn("cos", u_node)), n_num(a))
                    ))
                elseif fn_part.name == "cos" then
                    -- ∫ x*cos(ax+b) dx = cos(ax+b)/a^2 + x*sin(ax+b)/a
                    return ast_simplify(n_bin("+",
                        n_bin("/", n_fn("cos", ast_clone(u_node)), n_num(a * a)),
                        n_bin("/", n_bin("*", n_var(), n_fn("sin", u_node)), n_num(a))
                    ))
                elseif fn_part.name == "ln" and math.abs(b) < 1e-11 then
                    -- ∫ x*ln(ax) dx = (x^2/2)*ln(ax) - x^2/4
                    return ast_simplify(n_bin("-",
                        n_bin("*", n_bin("/", n_bin("^", n_var(), n_num(2)), n_num(2)), n_fn("ln", u_node)),
                        n_bin("/", n_bin("^", n_var(), n_num(2)), n_num(4))
                    ))
                end
            end
        end
    end
    if node.op == "/" then
        if not has_var(node.r) then
            local il = ast_integrate(node.l)
            if il then return ast_simplify(n_bin("/", il, ast_clone(node.r))) end
        end
        -- Forma c / (a*x + b) -> (c/a) * ln(a*x + b)
        if not has_var(node.l) then
            local a, _ = match_linear(node.r)
            if a and math.abs(a) > 1e-11 then
                return ast_simplify(n_bin("*", n_bin("/", ast_clone(node.l), n_num(a)), n_fn("ln", ast_clone(node.r))))
            end
            -- Forma c / x^n -> c * x^(1-n) / (1-n)
            if node.r.op == "^" and node.r.l.op == "var" and is_num(node.r.r) then
                local n_exp = -node.r.r.val
                if math.abs(n_exp + 1) < 1e-11 then
                    return ast_simplify(n_bin("*", ast_clone(node.l), n_fn("ln", n_var())))
                else
                    return ast_simplify(n_bin("/",
                        n_bin("*", ast_clone(node.l), n_bin("^", n_var(), n_num(n_exp + 1))),
                        n_num(n_exp + 1)
                    ))
                end
            end
        end
        -- Forma f'(x) / f(x) -> ln(f(x))
        local df = ast_simplify(ast_diff(node.r))
        if ast_equal(node.l, df) then
            return n_fn("ln", ast_clone(node.r))
        end
    end
    if node.op == "^" then
        local a, _ = match_linear(node.l)
        if a and math.abs(a) > 1e-11 and is_num(node.r) then
            local n_val = node.r.val
            if math.abs(n_val + 1) < 1e-11 then
                return ast_simplify(n_bin("/", n_fn("ln", ast_clone(node.l)), n_num(a)))
            else
                return ast_simplify(n_bin("/",
                    n_bin("^", ast_clone(node.l), n_num(n_val + 1)),
                    n_num(a * (n_val + 1))
                ))
            end
        end
        -- Forma c^(a*x + b) -> c^(a*x+b) / (a * ln(c))
        local a_exp, _ = match_linear(node.r)
        if not has_var(node.l) and a_exp and math.abs(a_exp) > 1e-11 then
            local base_v = ast_eval(node.l, 0)
            if base_v > 0 then
                return ast_simplify(n_bin("/", ast_clone(node), n_num(a_exp * math.log(base_v))))
            end
        end
    end
    if node.op == "fn" then
        local a, _ = match_linear(node.arg)
        if a and math.abs(a) > 1e-11 then
            local u = ast_clone(node.arg)
            local fn = node.name
            if fn == "sin" then
                return ast_simplify(n_un("neg", n_bin("/", n_fn("cos", u), n_num(a))))
            elseif fn == "cos" then
                return ast_simplify(n_bin("/", n_fn("sin", u), n_num(a)))
            elseif fn == "tan" then
                return ast_simplify(n_un("neg", n_bin("/", n_fn("ln", n_fn("cos", u)), n_num(a))))
            elseif fn == "exp" then
                return ast_simplify(n_bin("/", n_fn("exp", u), n_num(a)))
            elseif fn == "sqrt" then
                return ast_simplify(n_bin("/",
                    n_bin("*", n_num(2), n_bin("^", u, n_num(1.5))),
                    n_num(3 * a)
                ))
            elseif fn == "ln" then
                -- ∫ ln(ax+b) dx = ((ax+b)*ln(ax+b) - (ax+b)) / a
                return ast_simplify(n_bin("/",
                    n_bin("-", n_bin("*", ast_clone(u), n_fn("ln", ast_clone(u))), u),
                    n_num(a)
                ))
            end
        end
    end
    return nil
end

-- Cuadratura numérica de Simpson compuesta para integrales definidas ∫_a^b f(x) dx
local function simpson_integrate(ast_node, a, b, intervals)
    local n = intervals or 200
    if n % 2 == 1 then n = n + 1 end
    local h = (b - a) / n
    local sum_val = 0
    local sum_abs = 0

    for i = 0, n do
        local x = a + i * h
        local ok, fx = pcall(ast_eval, ast_node, x)
        if not ok or type(fx) ~= "number" or fx ~= fx or math.abs(fx) == math.huge then
            return nil, nil
        end
        local w = (i == 0 or i == n) and 1 or ((i % 2 == 1) and 4 or 2)
        sum_val = sum_val + w * fx
        sum_abs = sum_abs + w * math.abs(fx)
    end

    return (h / 3.0) * sum_val, (h / 3.0) * sum_abs
end

-- ============================================================================
-- TABLAS DE MODOS FINANCIEROS, DERIVADOS Y ESTADÍSTICA
-- ============================================================================
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
                { k = "i", label = "i efectivo anual (0 si ik)", def = "0.06" },
                { k = "ik", label = "ik fraccionado (0 si i)", def = "0" },
                { k = "k", label = "k (Frec: 12 mes, 4 trim)", def = "12" },
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
    deriv = {
        {
            id = "bs",
            name = "Black-Scholes & Griegas",
            formula = "C = S0·e^(-qT)·N(d1) - K·e^(-rT)·N(d2)  |  P = K·e^(-rT)·N(-d2) - S0·e^(-qT)·N(-d1)",
            fields = {
                { k = "S0", label = "S0 (Precio Spot activo)", def = "100" },
                { k = "K", label = "K (Precio Strike)", def = "100" },
                { k = "r", label = "r (Tipo libre riesgo)", def = "0.05" },
                { k = "sigma", label = "σ (Volatilidad anual)", def = "0.20" },
                { k = "T", label = "T (Tiempo en años)", def = "1" },
                { k = "q", label = "q (Tasa dividendo cont.)", def = "0" },
            },
        },
        {
            id = "binom_par",
            name = "Binomial CRR & Paridad",
            formula = "u = e^(σ√Δt), d = 1/u, p = (e^(rΔt)-d)/(u-d)  |  Paridad: C - P = S0 - K·e^(-rT)",
            fields = {
                { k = "S0", label = "S0 (Precio Spot activo)", def = "100" },
                { k = "K", label = "K (Precio Strike)", def = "100" },
                { k = "r", label = "r (Tipo libre riesgo)", def = "0.05" },
                { k = "sigma", label = "σ (Volatilidad anual)", def = "0.20" },
                { k = "T", label = "T (Tiempo en años)", def = "1" },
                { k = "steps", label = "N (Pasos árbol binomial)", def = "40" },
            },
        },
        {
            id = "fut_fra",
            name = "Futuros, Forward & FRA",
            formula = "Futuro: F0 = S0·e^((r-q)T)  |  FRA Liq: N·(rM - rK)·T / (1 + rM·T)",
            fields = {
                { k = "S0", label = "S0 (Spot) o Nominal FRA", def = "1000" },
                { k = "r", label = "r (Interés / rM mercado)", def = "0.05" },
                { k = "q", label = "q (Dividendo / rK FRA)", def = "0.035" },
                { k = "T", label = "T (Plazo en años)", def = "0.5" },
                { k = "Kant", label = "K (Precio Forward pact.)", def = "990" },
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

local CALC_FIELDS = {
    { k = "fx", label = "f(x)", is_expr = true },
    { k = "x0", label = "x0 (Punto derivada)", is_expr = false },
    { k = "a", label = "a (Límite inf. ∫a..b)", is_expr = false },
    { k = "b", label = "b (Límite sup. ∫a..b)", is_expr = false },
}

local CALC_PRESETS = {
    { name = "Ej. Polin", fx = "x^3 - 3*x^2 + 2*x", x0 = "2", a = "0", b = "3" },
    { name = "Ej. Trig", fx = "sin(2*x) + cos(x)", x0 = "0", a = "0", b = "1.5708" },
    { name = "Ej. Exp", fx = "x*exp(x)", x0 = "1", a = "0", b = "2" },
    { name = "Ej. Rac/Ln", fx = "4/(2*x + 1) + ln(x)", x0 = "1", a = "1", b = "4" },
}

function SarrikoCalc:init()
    -- Pestañas: "poly", "sys", "stat", "calc", "cap", "rent", "loan", "deriv"
    self.tab = "deriv"
    self.show_formula = true
    self.fresh_field = true
    self.window = nil

    -- 1. Polinomios (Grado 2, 3, 4)
    self.poly_deg = 2
    self.poly_coeffs = { "1", "-5", "6", "0", "0" }
    self.poly_sel = 1

    -- 2. Sistemas Lineales NxN (2x2 a 6x6: x, y, z, a, b, c)
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

    -- 3. Finanzas y Derivados Financieros (Call / Put / Futuros)
    self.fin_sub = { cap = 1, rent = 1, loan = 1, deriv = 1 }
    self.fin_vals = {}
    self.fin_sel = 1
    self:_initFinDefaults()

    -- 4. Estadística y Probabilidad
    self.stat_sub = 1
    self.stat1_n = 5
    self.stat1_mode = "x"
    self.stat1_sel = 1
    self.stat1_x = { "10", "12", "15", "18", "20", "22", "25", "30" }
    self.stat1_f = { "1", "2", "4", "2", "1", "1", "1", "1" }

    self.stat2_n = 4
    self.stat2_mode = "x"
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

    -- 5. Cálculo Simbólico y Numérico (Derivadas e Integrales definidas/indefinidas)
    self.calc_sub = 1 -- 1 = Derivadas, 2 = Integrales, 3 = Ambos resumidos
    self.calc_sel = 1
    self.calc_vals = {
        fx = "x^3 - 3*x^2 + 2*x",
        x0 = "2",
        a = "0",
        b = "3",
    }

    self.result_lines = {}
    self:_recalculate()

    self.ui.menu:registerToMainMenu(self)
end

function SarrikoCalc:addToMainMenu(menu_items)
    menu_items.sarriko = {
        text = _("Calculadora Financiera, Derivados, Cálculo y Estadística"),
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
        face = Font:getFace("cfont", font_size or 15),
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

function SarrikoCalc:_isEditingFunctionExpr()
    return (self.tab == "calc") and (self.calc_sel == 1)
end

function SarrikoCalc:_getActiveString()
    if self.tab == "poly" then
        return self.poly_coeffs[self.poly_sel] or "0"
    elseif self.tab == "sys" then
        return self.sys_mat[self.sys_eq][self.sys_col] or "0"
    elseif self.tab == "calc" then
        local f = CALC_FIELDS[self.calc_sel] or CALC_FIELDS[1]
        return self.calc_vals[f.k] or "0"
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
    elseif self.tab == "calc" then
        local f = CALC_FIELDS[self.calc_sel] or CALC_FIELDS[1]
        self.calc_vals[f.k] = str
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
    local is_expr = self:_isEditingFunctionExpr()

    if key == "CLR" then
        self:_setActiveString(is_expr and "x" or "0")
        self.fresh_field = true
    elseif key == "DEL" then
        if #cur <= 1 or (not is_expr and #cur == 2 and string.sub(cur, 1, 1) == "-") then
            self:_setActiveString(is_expr and "x" or "0")
            self.fresh_field = true
        else
            self:_setActiveString(string.sub(cur, 1, -2))
            self.fresh_field = false
        end
    elseif key == "+/-" then
        if is_expr then
            self:_setActiveString(cur .. "-")
            self.fresh_field = false
        else
            if string.sub(cur, 1, 1) == "-" then
                self:_setActiveString(string.sub(cur, 2))
            elseif cur ~= "0" then
                self:_setActiveString("-" .. cur)
            end
        end
    elseif key == "." then
        if self.fresh_field and not is_expr then
            self:_setActiveString("0.")
            self.fresh_field = false
        elseif is_expr or not string.find(cur, "%.") then
            self:_setActiveString(cur .. ".")
            self.fresh_field = false
        end
    elseif key == "NEXT" then
        self:_advanceField()
    else
        if self.fresh_field then
            -- En expresiones algebraicas, si pulsa un operador binario (+, -, *, /, ^) tras seleccionar,
            -- lo añade al final en vez de borrar la función entera
            if is_expr and (key == "+" or key == "-" or key == "*" or key == "/" or key == "^") then
                self:_setActiveString(cur .. key)
            else
                self:_setActiveString(key)
            end
            self.fresh_field = false
        else
            if not is_expr and cur == "0" then
                self:_setActiveString(key)
            else
                self:_setActiveString(cur .. key)
            end
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
    elseif self.tab == "calc" then
        self.calc_sel = (self.calc_sel % #CALC_FIELDS) + 1
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

-- ============================================================================
-- CÁLCULO DE DERIVADAS (SIMBÓLICAS Y EN X0) E INTEGRALES (SIMBÓLICAS Y DEFINIDAS)
-- ============================================================================
function SarrikoCalc:_calcCalculus()
    local fx_str = self.calc_vals.fx or "x"
    local x0 = tonumber(self.calc_vals.x0) or 0
    local a = tonumber(self.calc_vals.a) or 0
    local b = tonumber(self.calc_vals.b) or 1

    local ast = parse_expr(fx_str)
    if not ast then
        self.result_lines = { _("Expresión f(x) incompleta o con paréntesis sin cerrar.") }
        return
    end

    local d1_ast = ast_simplify(ast_diff(ast))
    local d2_ast = ast_simplify(ast_diff(d1_ast))
    local int_ast = ast_integrate(ast)

    local d1_str = ast_tostring(d1_ast)
    local d2_str = ast_tostring(d2_ast)
    local int_str = int_ast and (ast_tostring(int_ast) .. " + C") or "No elemental (Cuadratura numérica activa)"

    local ok_f, fx0 = pcall(ast_eval, ast, x0)
    local ok_d1, dfx0 = pcall(ast_eval, d1_ast, x0)
    local ok_d2, d2fx0 = pcall(ast_eval, d2_ast, x0)

    local eval_str
    local tang_str
    if ok_f and ok_d1 and ok_d2 and fx0 == fx0 and dfx0 == dfx0 then
        local curv = (d2fx0 > 1e-9) and "Convexa ∪" or ((d2fx0 < -1e-9) and "Cóncava ∩" or "Inflexión")
        eval_str = string.format(
            "En x0=%.4g:  f(x0) = %.5g  |  f'(x0) = %.5g  |  f''(x0) = %.5g (%s)",
            x0, fx0, dfx0, d2fx0, curv
        )
        local n_ord = fx0 - dfx0 * x0
        tang_str = string.format(
            "Recta Tangente en x0=%.4g:   y = %.5g·x %s %.5g",
            x0, dfx0, n_ord >= 0 and "+" or "-", math.abs(n_ord)
        )
    else
        eval_str = string.format("En x0=%.4g: Punto fuera del dominio de f(x).", x0)
        tang_str = "Recta Tangente: No definida en ese punto."
    end

    local def_val, abs_area = simpson_integrate(ast, a, b, 200)
    local def_str, area_str
    if def_val then
        local avg_val = (math.abs(b - a) > 1e-12) and (def_val / (b - a)) or fx0
        def_str = string.format("Integral Definida ∫[%.4g → %.4g] f(x)dx = %s", a, b, to_frac_str(def_val))
        area_str = string.format("Área Geométrica ∫|f(x)|dx = %.6g   |   Valor Medio μ = %.5g", abs_area, avg_val)
    else
        def_str = string.format("Integral Definida ∫[%.4g → %.4g]: Asíntota o fuera de dominio en [a,b].", a, b)
        area_str = "Elige un intervalo [a, b] donde f(x) sea continua."
    end

    if self.calc_sub == 1 then
        self.result_lines = {
            string.format("Derivada 1ª:  f'(x) = %s", d1_str),
            string.format("Derivada 2ª:  f''(x) = %s", d2_str),
            eval_str,
            tang_str,
        }
    elseif self.calc_sub == 2 then
        self.result_lines = {
            string.format("Primitiva Indefinida:  ∫ f(x)dx = %s", int_str),
            def_str,
            area_str,
        }
    else
        self.result_lines = {
            string.format("f'(x) = %s   |   f'(%.4g) = %s", d1_str, x0, ok_d1 and to_frac_str(dfx0) or "Err"),
            string.format("∫ f(x)dx = %s", int_str),
            def_str .. (abs_area and string.format("  (Área |f| = %.5g)", abs_area) or ""),
        }
    end
end

-- ============================================================================
-- CÁLCULO DE DERIVADOS FINANCIEROS (BLACK-SCHOLES, GRIEGAS, BINOMIAL, FUTUROS)
-- ============================================================================
function SarrikoCalc:_calcDerivativesFin()
    local sub_idx = self.fin_sub.deriv
    local mode = FIN_MODES.deriv[sub_idx]
    local raw = self.fin_vals.deriv[sub_idx]
    local v = {}
    for k, str in pairs(raw) do v[k] = tonumber(str) or 0 end

    if mode.id == "bs" then
        local S0, K, r, sigma, T, q = v.S0, v.K, v.r, v.sigma, v.T, v.q
        if S0 <= 0 or K <= 0 or sigma <= 0 or T <= 0 then
            self.result_lines = { _("Parámetros requeridos: S0 > 0, K > 0, σ > 0 y T > 0.") }
            return
        end

        local sqT = math.sqrt(T)
        local d1 = (math.log(S0 / K) + (r - q + 0.5 * sigma * sigma) * T) / (sigma * sqT)
        local d2 = d1 - sigma * sqT

        local Nd1 = norm_cdf(d1)
        local Nd2 = norm_cdf(d2)
        local Nmd1 = norm_cdf(-d1)
        local Nmd2 = norm_cdf(-d2)
        local nd1 = norm_pdf(d1)

        local eqT = math.exp(-q * T)
        local erT = math.exp(-r * T)

        local call_p = S0 * eqT * Nd1 - K * erT * Nd2
        local put_p = K * erT * Nmd2 - S0 * eqT * Nmd1

        -- Las Griegas (The Greeks)
        local delta_c = eqT * Nd1
        local delta_p = -eqT * Nmd1
        local gamma = (eqT * nd1) / (S0 * sigma * sqT)
        local vega = S0 * eqT * nd1 * sqT
        local theta_c = -(S0 * sigma * eqT * nd1) / (2 * sqT) - r * K * erT * Nd2 + q * S0 * eqT * Nd1
        local theta_p = -(S0 * sigma * eqT * nd1) / (2 * sqT) + r * K * erT * Nmd2 - q * S0 * eqT * Nmd1
        local rho_c = K * T * erT * Nd2
        local rho_p = -K * T * erT * Nmd2

        self.result_lines = {
            string.format("CALL = %.4f €  |  PUT = %.4f €  |  d1=%.4f, d2=%.4f  |  P(ITM)=%.1f%%",
                call_p, put_p, d1, d2, Nd2 * 100),
            string.format("Δ Call = %.4f  |  Δ Put = %.4f  |  Γ Gamma = %.5f  |  Vega = %.3f (1%%: %.3f)",
                delta_c, delta_p, gamma, vega, vega * 0.01),
            string.format("Θ Call = %.3f/año (%.4f/día)  |  Θ Put = %.3f/año  |  ρ Call=%.3f, ρ Put=%.3f",
                theta_c, theta_c / 365, theta_p, rho_c, rho_p),
        }

    elseif mode.id == "binom_par" then
        local S0, K, r, sigma, T = v.S0, v.K, v.r, v.sigma, v.T
        local N = math.max(1, math.min(200, math.floor(v.steps + 0.5)))
        if S0 <= 0 or K <= 0 or sigma <= 0 or T <= 0 then
            self.result_lines = { _("Parámetros requeridos: S0 > 0, K > 0, σ > 0 y T > 0.") }
            return
        end

        local dt = T / N
        local u = math.exp(sigma * math.sqrt(dt))
        local d = 1.0 / u
        local disc = math.exp(-r * dt)
        local p = (math.exp(r * dt) - d) / (u - d)

        if p <= 0 or p >= 1 then
            self.result_lines = { _("Condición de no arbitraje violada: ajusta r, σ o el número de pasos N.") }
            return
        end

        local c_eur, p_eur, c_ame, p_ame = {}, {}, {}, {}
        for i = 0, N do
            local ST = S0 * (u ^ (N - i)) * (d ^ i)
            c_eur[i] = math.max(0, ST - K)
            p_eur[i] = math.max(0, K - ST)
            c_ame[i] = c_eur[i]
            p_ame[i] = p_eur[i]
        end

        for step = N - 1, 0, -1 do
            for i = 0, step do
                local S_node = S0 * (u ^ (step - i)) * (d ^ i)
                c_eur[i] = disc * (p * c_eur[i] + (1 - p) * c_eur[i + 1])
                p_eur[i] = disc * (p * p_eur[i] + (1 - p) * p_eur[i + 1])
                c_ame[i] = math.max(S_node - K, disc * (p * c_ame[i] + (1 - p) * c_ame[i + 1]))
                p_ame[i] = math.max(K - S_node, disc * (p * p_ame[i] + (1 - p) * p_ame[i + 1]))
            end
        end

        local intr_c = math.max(0, S0 - K)
        local intr_p = math.max(0, K - S0)
        local tv_c = math.max(0, c_eur[0] - intr_c)
        local tv_p = math.max(0, p_eur[0] - intr_p)
        local moneyness = math.abs(S0 - K) < 1e-6 and "ATM" or ((S0 > K) and "Call ITM / Put OTM" or "Call OTM / Put ITM")

        self.result_lines = {
            string.format("CRR (N=%d): u=%.4f, d=%.4f, p=%.4f  |  Estado: %s", N, u, d, p, moneyness),
            string.format("Europea: Call=%.4f €, Put=%.4f €  |  Americana: Call=%.4f €, Put=%.4f €",
                c_eur[0], p_eur[0], c_ame[0], p_ame[0]),
            string.format("V.Intrínseco C=%.2f/P=%.2f | V.Temporal C=%.2f/P=%.2f | Breakeven: C=%.2f, P=%.2f",
                intr_c, intr_p, tv_c, tv_p, K + c_eur[0], K - p_eur[0]),
        }

    elseif mode.id == "fut_fra" then
        local S0, r, q, T, Kant = v.S0, v.r, v.q, v.T, v.Kant
        local F_cont = S0 * math.exp((r - q) * T)
        local F_comp = S0 * ((1 + r - q) ^ T)
        local basis = S0 - F_cont
        local V_fwd = (F_cont - Kant) * math.exp(-r * T)
        -- Interpretación alternativa como FRA: S0 = Nominal, r = rM mercado, q = rK garantizado, T = plazo
        local fra_liq = (1 + r * T ~= 0) and ((S0 * (r - q) * T) / (1 + r * T)) or 0

        self.result_lines = {
            string.format("Futuro/Forward Teórico:  Cont. F0 = %.4f €  |  Comp. F0 = %.4f €  |  Base = %.4f",
                F_cont, F_comp, basis),
            string.format("Valor Forward en curso (Strike K=%.2f):  Vt = %.4f € ( Largo ) / %.4f € ( Corto )",
                Kant, V_fwd, -V_fwd),
            string.format("Liquidación FRA (Nominal=%.0f, rM=%.2f%%, rK=%.2f%%):  %.2f €",
                S0, r * 100, q * 100, fra_liq),
        }
    end
end

-- ============================================================================
-- POLINOMIOS, SISTEMAS NxN, ESTADÍSTICA Y FINANZAS SARRIKO
-- ============================================================================
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
        if c_abs(cr) > c_abs(z_pick) then z_pick = cr end
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
        if i <= 3 then table.insert(line1, item) else table.insert(line2, item) end
    end

    self.result_lines = {
        string.format("Sistema Compatible Determinado   |   det(A) = %.5g", det),
        table.concat(line1, "    |    "),
    }
    if #line2 > 0 then
        table.insert(self.result_lines, table.concat(line2, "    |    "))
    end
end

function SarrikoCalc:_calcStatistics()
    if self.stat_sub == 1 then
        local pairs_list = {}
        local N, sum_x, sum_x2 = 0, 0, 0
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

        local mx, my = sx / n, sy / n
        local vx = math.max(0, (sxx / n) - mx * mx)
        local vy = math.max(0, (syy / n) - my * my)
        local sdx, sdy = math.sqrt(vx), math.sqrt(vy)
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
        local cdf_le, cdf_lt, p_inter = 0, 0, 0
        local lo, hi = math.min(k1, k), math.max(k1, k)

        for i = 0, n do
            local pr = binom_pmf(n, i, p)
            if i < k then cdf_lt = cdf_lt + pr end
            if i <= k then cdf_le = cdf_le + pr end
            if i >= lo and i <= hi then p_inter = p_inter + pr end
        end

        self.result_lines = {
            string.format("Media E[X] = %.4g   |   Varianza V[X] = %.4g   |   Desv. σ = %.4g", ex, vx, sdx),
            string.format("Puntual P(X = %d) = %.6f   |   Intervalo P(%d ≤ X ≤ %d) = %.6f", k, pmf_k, lo, hi, p_inter),
            string.format("Acum: P(X≤%d)=%.5f | P(X<%d)=%.5f | Cola: P(X≥%d)=%.5f | P(X>%d)=%.5f",
                k, cdf_le, k, cdf_lt, k, math.max(0, 1 - cdf_lt), k, math.max(0, 1 - cdf_le)),
        }

    elseif self.stat_sub == 5 then
        local raw = self.dist_vals[5]
        local lambda = tonumber(raw.lambda) or 1
        local k = math.floor((tonumber(raw.k) or 0) + 0.5)
        local k1 = math.floor((tonumber(raw.k1) or 0) + 0.5)

        if lambda <= 0 or k < 0 or k > 5000 then
            self.result_lines = { _("Parámetros requeridos: λ > 0  y  0 ≤ k ≤ 5000.") }
            return
        end

        local pmf_k = pois_pmf(lambda, k)
        local cdf_le, cdf_lt, p_inter = 0, 0, 0
        local lo, hi = math.max(0, math.min(k1, k)), math.max(k1, k)

        for i = 0, math.max(k, hi) do
            local pr = pois_pmf(lambda, i)
            if i < k then cdf_lt = cdf_lt + pr end
            if i <= k then cdf_le = cdf_le + pr end
            if i >= lo and i <= hi then p_inter = p_inter + pr end
        end

        self.result_lines = {
            string.format("Media E[X] = λ = %.4g   |   Varianza V[X] = %.4g   |   Desv. σ = √λ = %.4g",
                lambda, lambda, math.sqrt(lambda)),
            string.format("Puntual P(X = %d) = %.6f   |   Intervalo P(%d ≤ X ≤ %d) = %.6f", k, pmf_k, lo, hi, p_inter),
            string.format("Acum: P(X≤%d)=%.5f | P(X<%d)=%.5f | Cola: P(X≥%d)=%.5f | P(X>%d)=%.5f",
                k, cdf_le, k, cdf_lt, k, math.max(0, 1 - cdf_lt), k, math.max(0, 1 - cdf_le)),
        }
    end
end

function SarrikoCalc:_calcFinancial()
    if self.tab == "deriv" then
        self:_calcDerivativesFin()
        return
    end

    local cat = self.tab
    local sub_idx = self.fin_sub[cat]
    local mode = FIN_MODES[cat][sub_idx]
    local raw = self.fin_vals[cat][sub_idx]
    local v = {}
    for k, str in pairs(raw) do v[k] = tonumber(str) or 0 end

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
        local perp = (M / i) * frac_corr
        self.result_lines = {
            string.format("a_n|i = %.6f   |   s_n|i = %.6f   |   Perpetua Va_∞ = %.2f €", ani, sni, perp),
            string.format("Pospagable:  Va = %.2f €   |   Vs = %.2f €", Va, Vs),
            string.format("Prepagable (ä, s̈):  Vä = %.2f €   |   Vs̈ = %.2f €", Va * (1 + i), Vs * (1 + i)),
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
            for j = 1, 4 do val = val + Q[j] * ((1 + rate) ^ (-j)) end
            return val
        end
        local van = npv(k)
        local r0, r1 = 0.05, 0.15
        local tir_ok = false
        for _ = 1, 60 do
            local f0, f1 = npv(r0), npv(r1)
            if math.abs(f1) < 1e-7 then tir_ok = true; break end
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
                payback_str = string.format("%.2f años", (j - 1) + (I0 - prev) / Q[j])
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
    elseif self.tab == "calc" then
        self:_calcCalculus()
    else
        self:_calcFinancial()
    end
end

-- ============================================================================
-- CONSTRUCCIÓN DE INTERFAZ Y TECLADO DINÁMICO ALGEBRAICO/NUMÉRICO
-- ============================================================================
function SarrikoCalc:_buildBodySection(panel_w, sub_h, field_h)
    local rows = VerticalGroup:new({ align = "center" })

    if self.tab == "poly" then
        local w3 = math.floor((panel_w - 18) / 3)
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton(self.poly_deg == 2 and "• Grado 2 (ax²+bx+c) •" or "Grado 2", function()
                self.poly_deg = 2; self.poly_sel = 1; self.fresh_field = true; self:_recalculate(); self:show()
            end, w3, sub_h, self.poly_deg == 2 and 4 or 1),
            self:_makeButton(self.poly_deg == 3 and "• Grado 3 (ax³+...) •" or "Grado 3", function()
                self.poly_deg = 3; self.poly_sel = 1; self.fresh_field = true; self:_recalculate(); self:show()
            end, w3, sub_h, self.poly_deg == 3 and 4 or 1),
            self:_makeButton(self.poly_deg == 4 and "• Grado 4 (ax⁴+...) •" or "Grado 4", function()
                self.poly_deg = 4; self.poly_sel = 1; self.fresh_field = true; self:_recalculate(); self:show()
            end, w3, sub_h, self.poly_deg == 4 and 4 or 1),
        }))

        local labels = {
            [2] = { "a (x²)", "b (x)", "c (indep)" },
            [3] = { "a (x³)", "b (x²)", "c (x)", "d (indep)" },
            [4] = { "a (x⁴)", "b (x³)", "c (x²)", "d (x)", "e (indep)" },
        }
        local cur_labels = labels[self.poly_deg]
        local btn_w = math.floor((panel_w - 16) / 2)

        for i = 1, #cur_labels, 2 do
            local line = HorizontalGroup:new({ align = "center" })
            for j = i, math.min(i + 1, #cur_labels) do
                local is_sel = (self.poly_sel == j)
                local txt = string.format("%s%s = %s", is_sel and "▶ " or "", cur_labels[j], self.poly_coeffs[j])
                table.insert(line, self:_makeButton(txt, function()
                    self.poly_sel = j; self.fresh_field = true; self:show()
                end, btn_w, field_h, is_sel and 4 or 2))
            end
            table.insert(rows, line)
        end

    elseif self.tab == "sys" then
        local w5 = math.floor((panel_w - 24) / 5)
        local size_row = HorizontalGroup:new({ align = "center" })
        local size_labels = { [2] = "2×2 (x,y)", [3] = "3×3 (..z)", [4] = "4×4 (..a)", [5] = "5×5 (..b)", [6] = "6×6 (..c)" }
        for sz = 2, 6 do
            local active = (self.sys_n == sz)
            table.insert(size_row, self:_makeButton(active and ("•" .. size_labels[sz] .. "•") or size_labels[sz], function()
                self.sys_n = sz; self.sys_eq = 1; self.sys_col = 1; self.fresh_field = true; self:_recalculate(); self:show()
            end, w5, sub_h, active and 4 or 1))
        end
        table.insert(rows, size_row)

        local nav_w = math.floor((panel_w - 18) / 3)
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton("◀ Ecuación Ant.", function()
                self.sys_eq = ((self.sys_eq - 2) % self.sys_n) + 1; self.fresh_field = true; self:show()
            end, nav_w, sub_h, 2),
            self:_makeText(string.format("Editando Ecuación %d de %d", self.sys_eq, self.sys_n), 16),
            self:_makeButton("Ecuación Sig. ▶", function()
                self.sys_eq = (self.sys_eq % self.sys_n) + 1; self.fresh_field = true; self:show()
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
                self.sys_col = c; self.fresh_field = true; self:show()
            end, col_w, field_h, is_sel and 4 or 2)

            if c <= 4 then table.insert(coeff_row1, btn) else table.insert(coeff_row2, btn) end
        end
        table.insert(rows, coeff_row1)
        if n_cols > 4 then table.insert(rows, coeff_row2) end

        for r = 1, self.sys_n do
            local parts = {}
            for c = 1, self.sys_n do table.insert(parts, self.sys_mat[r][c] .. VAR_NAMES[c]) end
            local eq_str = string.format("%sEc.%d:  %s = %s",
                r == self.sys_eq and "▶ " or "   ", r, table.concat(parts, " + "), self.sys_mat[r][7])
            table.insert(rows, self:_makeText(eq_str, 13))
        end

    elseif self.tab == "calc" then
        local w3 = math.floor((panel_w - 18) / 3)
        local w4 = math.floor((panel_w - 20) / 4)

        -- Submodos: Derivadas, Integrales o Vista combinada
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton(self.calc_sub == 1 and "• Derivadas f'(x) •" or "Derivadas f'(x)", function()
                self.calc_sub = 1; self:_recalculate(); self:show()
            end, w3, sub_h, self.calc_sub == 1 and 4 or 1),
            self:_makeButton(self.calc_sub == 2 and "• Integrales ∫f(x) •" or "Integrales ∫f(x)", function()
                self.calc_sub = 2; self:_recalculate(); self:show()
            end, w3, sub_h, self.calc_sub == 2 and 4 or 1),
            self:_makeButton(self.calc_sub == 3 and "• Ambos (f' y ∫) •" or "Ambos (f' y ∫)", function()
                self.calc_sub = 3; self:_recalculate(); self:show()
            end, w3, sub_h, self.calc_sub == 3 and 4 or 1),
        }))

        -- Botones de ejemplos rápidos (Presets)
        local preset_row = HorizontalGroup:new({ align = "center" })
        for _, pr in ipairs(CALC_PRESETS) do
            table.insert(preset_row, self:_makeButton(pr.name, function()
                self.calc_vals.fx = pr.fx
                self.calc_vals.x0 = pr.x0
                self.calc_vals.a = pr.a
                self.calc_vals.b = pr.b
                self.fresh_field = true
                self:_recalculate()
                self:show()
            end, w4, math.max(30, math.floor(sub_h * 0.9)), 1))
        end
        table.insert(rows, preset_row)

        -- Botón de ancho completo para f(x)
        local fx_sel = (self.calc_sel == 1)
        table.insert(rows, self:_makeButton(
            string.format("%sf(x) = %s", fx_sel and "▶ " or "", self.calc_vals.fx),
            function()
                self.calc_sel = 1; self.fresh_field = true; self:show()
            end,
            panel_w - 10, field_h, fx_sel and 4 or 2
        ))

        -- Fila con x0 (punto derivada), a (lím. inf) y b (lím. sup)
        table.insert(rows, HorizontalGroup:new({
            align = "center",
            self:_makeButton(
                string.format("%sx0 (Deriv): %s", self.calc_sel == 2 and "▶ " or "", self.calc_vals.x0),
                function() self.calc_sel = 2; self.fresh_field = true; self:show() end,
                w3, field_h, self.calc_sel == 2 and 4 or 2
            ),
            self:_makeButton(
                string.format("%sa (∫ inf): %s", self.calc_sel == 3 and "▶ " or "", self.calc_vals.a),
                function() self.calc_sel = 3; self.fresh_field = true; self:show() end,
                w3, field_h, self.calc_sel == 3 and 4 or 2
            ),
            self:_makeButton(
                string.format("%sb (∫ sup): %s", self.calc_sel == 4 and "▶ " or "", self.calc_vals.b),
                function() self.calc_sel = 4; self.fresh_field = true; self:show() end,
                w3, field_h, self.calc_sel == 4 and 4 or 2
            ),
        }))

    elseif self.tab == "stat" then
        local w5 = math.floor((panel_w - 24) / 5)
        local sub_labels = { "1-Var (x,n)", "2-Var Reg", "Normal", "Binomial", "Poisson" }
        local sub_row = HorizontalGroup:new({ align = "center" })
        for s_idx, s_name in ipairs(sub_labels) do
            local active = (self.stat_sub == s_idx)
            table.insert(sub_row, self:_makeButton(active and ("•" .. s_name .. "•") or s_name, function()
                self.stat_sub = s_idx; self.fresh_field = true; self:_recalculate(); self:show()
            end, w5, sub_h, active and 4 or 1))
        end
        table.insert(rows, sub_row)

        if self.stat_sub == 1 then
            local w3 = math.floor((panel_w - 18) / 3)
            table.insert(rows, HorizontalGroup:new({
                align = "center",
                self:_makeButton(string.format("Nº Datos: %d (+1)", self.stat1_n), function()
                    self.stat1_n = (self.stat1_n % 7) + 2
                    if self.stat1_sel > self.stat1_n then self.stat1_sel = 1 end
                    self.fresh_field = true; self:_recalculate(); self:show()
                end, w3, sub_h, 2),
                self:_makeButton(self.stat1_mode == "x" and "• Editando xi •" or "Editar xi", function()
                    self.stat1_mode = "x"; self.fresh_field = true; self:show()
                end, w3, sub_h, self.stat1_mode == "x" and 4 or 1),
                self:_makeButton(self.stat1_mode == "f" and "• Editando frec ni •" or "Editar frec ni", function()
                    self.stat1_mode = "f"; self.fresh_field = true; self:show()
                end, w3, sub_h, self.stat1_mode == "f" and 4 or 1),
            }))

            local btn_w = math.floor((panel_w - 20) / 4)
            local r1 = HorizontalGroup:new({ align = "center" })
            local r2 = HorizontalGroup:new({ align = "center" })
            for i = 1, self.stat1_n do
                local is_sel = (self.stat1_sel == i)
                local lbl = string.format("%sx%d=%s (n=%s)", is_sel and "▶" or "", i, self.stat1_x[i], self.stat1_f[i])
                local b = self:_makeButton(lbl, function()
                    self.stat1_sel = i; self.fresh_field = true; self:show()
                end, btn_w, field_h, is_sel and 4 or 2)
                if i <= 4 then table.insert(r1, b) else table.insert(r2, b) end
            end
            table.insert(rows, r1)
            if self.stat1_n > 4 then table.insert(rows, r2) end

        elseif self.stat_sub == 2 then
            local w4 = math.floor((panel_w - 20) / 4)
            table.insert(rows, HorizontalGroup:new({
                align = "center",
                self:_makeButton(string.format("Pares: %d (+1)", self.stat2_n), function()
                    self.stat2_n = (self.stat2_n - 1) % 5 + 2
                    if self.stat2_sel > self.stat2_n then self.stat2_sel = 1 end
                    self.fresh_field = true; self:_recalculate(); self:show()
                end, w4, sub_h, 2),
                self:_makeButton(self.stat2_mode == "x" and "• Edit X •" or "Edit X", function()
                    self.stat2_mode = "x"; self.fresh_field = true; self:show()
                end, w4, sub_h, self.stat2_mode == "x" and 4 or 1),
                self:_makeButton(self.stat2_mode == "y" and "• Edit Y •" or "Edit Y", function()
                    self.stat2_mode = "y"; self.fresh_field = true; self:show()
                end, w4, sub_h, self.stat2_mode == "y" and 4 or 1),
                self:_makeButton(self.stat2_mode == "x0" and ("▶ x0=" .. self.stat2_x0) or ("x0=" .. self.stat2_x0), function()
                    self.stat2_mode = "x0"; self.fresh_field = true; self:show()
                end, w4, sub_h, self.stat2_mode == "x0" and 4 or 1),
            }))

            local btn_w = math.floor((panel_w - 18) / 3)
            local r1 = HorizontalGroup:new({ align = "center" })
            local r2 = HorizontalGroup:new({ align = "center" })
            for i = 1, self.stat2_n do
                local is_sel = (self.stat2_mode ~= "x0") and (self.stat2_sel == i)
                local lbl = string.format("%s(%s ; %s)", is_sel and "▶" or "", self.stat2_x[i], self.stat2_y[i])
                local b = self:_makeButton(lbl, function()
                    if self.stat2_mode == "x0" then self.stat2_mode = "x" end
                    self.stat2_sel = i; self.fresh_field = true; self:show()
                end, btn_w, field_h, is_sel and 4 or 2)
                if i <= 3 then table.insert(r1, b) else table.insert(r2, b) end
            end
            table.insert(rows, r1)
            if self.stat2_n > 3 then table.insert(rows, r2) end

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
                        self.dist_sel = j; self.fresh_field = true; self:show()
                    end, btn_w, field_h, is_sel and 4 or 2))
                end
                table.insert(rows, line)
            end
        end

    else
        -- Pestañas Financieras y Derivados (Kapitala, Errentak, Mailegu, Deriv.Fin)
        local list = FIN_MODES[self.tab]
        local sub_idx = self.fin_sub[self.tab]
        local w_sub = math.floor((panel_w - 20) / #list)
        local sub_row = HorizontalGroup:new({ align = "center" })

        for idx, m in ipairs(list) do
            local active = (idx == sub_idx)
            table.insert(sub_row, self:_makeButton(active and ("•" .. m.name .. "•") or m.name, function()
                self.fin_sub[self.tab] = idx; self.fin_sel = 1; self.fresh_field = true; self:_recalculate(); self:show()
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
                    self.fin_sel = j; self.fresh_field = true; self:show()
                end, btn_w, field_h, is_sel and 4 or 2))
            end
            table.insert(rows, line)
        end
    end

    return rows
end

function SarrikoCalc:_getCurrentFormulaBanner()
    if self.tab == "poly" then
        if self.poly_deg == 2 then return "Fórmula:  a·x² + b·x + c = 0   →   x = (-b ± √(b² - 4ac)) / 2a"
        elseif self.poly_deg == 3 then return "Fórmula Cardano:  a·x³ + b·x² + c·x + d = 0"
        else return "Fórmula Ferrari:  a·x⁴ + b·x³ + c·x² + d·x + e = 0" end
    elseif self.tab == "sys" then
        return "Sistema Lineal A·X = B  (Variables: x, y, z, a, b, c) — Gauss con Pivoteo"
    elseif self.tab == "calc" then
        return "Cálculo: Regla Cadena/Producto/Cociente  |  Barrow ∫[a..b] f(x)dx = F(b) - F(a) & Simpson"
    elseif self.tab == "stat" then
        if self.stat_sub == 1 then return "1-Var:  x̄ = (∑xi·ni)/N  |  σ² = (∑xi²·ni)/N - x̄²  |  S² = σ²·N/(N-1)"
        elseif self.stat_sub == 2 then return "2-Var:  σxy = (∑xi·yi)/N - x̄·ȳ  |  r = σxy/(σx·σy)  |  y = a + b·x"
        else return DIST_MODES[self.stat_sub].formula end
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

    local is_expr = self:_isEditingFunctionExpr()

    local top_h = math.max(32, math.floor(screen_h * 0.044))
    local sub_h = math.max(32, math.floor(screen_h * 0.044))
    local field_h = math.max(35, math.floor(screen_h * 0.048))
    local key_h = math.max(36, math.floor(screen_h * (is_expr and 0.052 or 0.060)))

    local w4 = math.floor((panel_w - 20) / 4)
    local w5 = math.floor((panel_w - 24) / 5)
    local w6 = math.floor((panel_w - 26) / 6)

    -- 1. Cabecera
    local header_row = HorizontalGroup:new({
        align = "center",
        self:_makeText(_("SARRIKO FINANTZA, DERIVADOS, CÁLCULO & ESTAD."), 15),
        self:_makeButton(self.show_formula and _("Fórmula: SÍ") or _("Fórmula: NO"), function()
            self.show_formula = not self.show_formula; self:show()
        end, math.floor(panel_w * 0.22), top_h, 2),
        self:_makeButton(_("Salir"), function()
            self:_closeWindow(true)
        end, math.floor(panel_w * 0.15), top_h, 2),
    })

    -- 2. Barra de 8 Pestañas Principales en 2 filas de 4 (botones anchos y cómodos)
    local tabs_row1_defs = {
        { id = "poly", label = "Polinomios" },
        { id = "sys", label = "Sist. N×N" },
        { id = "stat", label = "Estadíst." },
        { id = "calc", label = "Cálculo ∫f'" },
    }
    local tabs_row2_defs = {
        { id = "cap", label = "Kapitala" },
        { id = "rent", label = "Errentak" },
        { id = "loan", label = "Mailegu/VAN" },
        { id = "deriv", label = "Deriv. Call/Put" },
    }

    local tab_row1 = HorizontalGroup:new({ align = "center" })
    for _, t in ipairs(tabs_row1_defs) do
        local active = (self.tab == t.id)
        table.insert(tab_row1, self:_makeButton(active and ("•" .. t.label .. "•") or t.label, function()
            self.tab = t.id; self.fresh_field = true; self:_recalculate(); self:show()
        end, w4, top_h, active and 4 or 1))
    end

    local tab_row2 = HorizontalGroup:new({ align = "center" })
    for _, t in ipairs(tabs_row2_defs) do
        local active = (self.tab == t.id)
        table.insert(tab_row2, self:_makeButton(active and ("•" .. t.label .. "•") or t.label, function()
            self.tab = t.id; self.fresh_field = true; self:_recalculate(); self:show()
        end, w4, top_h, active and 4 or 1))
    end

    -- 3. Cuerpo interactivo
    local body_section = self:_buildBodySection(panel_w, sub_h, field_h)

    -- 4. Pantalla de Fórmulas y Resultados
    local res_group = VerticalGroup:new({ align = "left" })
    if self.show_formula then
        table.insert(res_group, self:_makeText(self:_getCurrentFormulaBanner(), 12))
    end
    for _, line in ipairs(self.result_lines) do
        table.insert(res_group, self:_makeText("• " .. line, 14))
    end

    local result_box = FrameContainer:new({
        background = Blitbuffer.COLOR_WHITE,
        bordersize = 3,
        padding = 5,
        margin = 2,
        CenterContainer:new({
            dimen = Geom:new({ w = panel_w - 16, h = math.floor(screen_h * 0.165) }),
            res_group,
        }),
    })

    local layout = VerticalGroup:new({
        align = "center",
        header_row,
        tab_row1,
        tab_row2,
        body_section,
        result_box,
    })

    -- 5. Si estamos editando f(x) en la pestaña Cálculo, mostrar las 2 filas algebraicas
    if is_expr then
        local alg_row1 = HorizontalGroup:new({
            align = "center",
            self:_makeButton("x", function() self:_onKeyPress("x") end, w6, key_h, 3),
            self:_makeButton("^", function() self:_onKeyPress("^") end, w6, key_h, 2),
            self:_makeButton("sin(", function() self:_onKeyPress("sin(") end, w6, key_h, 2),
            self:_makeButton("cos(", function() self:_onKeyPress("cos(") end, w6, key_h, 2),
            self:_makeButton("tan(", function() self:_onKeyPress("tan(") end, w6, key_h, 2),
            self:_makeButton("ln(", function() self:_onKeyPress("ln(") end, w6, key_h, 2),
        })
        local alg_row2 = HorizontalGroup:new({
            align = "center",
            self:_makeButton("exp(", function() self:_onKeyPress("exp(") end, w6, key_h, 2),
            self:_makeButton("√(", function() self:_onKeyPress("sqrt(") end, w6, key_h, 2),
            self:_makeButton("(", function() self:_onKeyPress("(") end, w6, key_h, 2),
            self:_makeButton(")", function() self:_onKeyPress(")") end, w6, key_h, 2),
            self:_makeButton("+", function() self:_onKeyPress("+") end, w6, key_h, 2),
            self:_makeButton("*", function() self:_onKeyPress("*") end, w6, key_h, 2),
        })
        table.insert(layout, alg_row1)
        table.insert(layout, alg_row2)
    end

    -- 6. Teclado Numérico Principal
    local k_row1 = HorizontalGroup:new({
        align = "center",
        self:_makeButton("7", function() self:_onKeyPress("7") end, w5, key_h, 2),
        self:_makeButton("8", function() self:_onKeyPress("8") end, w5, key_h, 2),
        self:_makeButton("9", function() self:_onKeyPress("9") end, w5, key_h, 2),
        self:_makeButton(is_expr and "-" or "+/-", function() self:_onKeyPress("+/-") end, w5, key_h, 2),
        self:_makeButton("DEL", function() self:_onKeyPress("DEL") end, w5, key_h, 3),
    })

    local k_row2 = HorizontalGroup:new({
        align = "center",
        self:_makeButton("4", function() self:_onKeyPress("4") end, w5, key_h, 2),
        self:_makeButton("5", function() self:_onKeyPress("5") end, w5, key_h, 2),
        self:_makeButton("6", function() self:_onKeyPress("6") end, w5, key_h, 2),
        self:_makeButton(is_expr and "/" or ".", function()
            self:_onKeyPress(is_expr and "/" or ".")
        end, w5, key_h, 2),
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

    table.insert(layout, k_row1)
    table.insert(layout, k_row2)
    table.insert(layout, k_row3)

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