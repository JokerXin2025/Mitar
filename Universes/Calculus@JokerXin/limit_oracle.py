# limit_oracle.py
import sys
import sympy as sp
import json

def sympy_to_lean(expr):
    """将 SymPy 的表达式转换为 Lean 4 认识的语法"""
    s = str(expr)
    s = s.replace('**', '^') # Lean 用 ^ 表示乘方
    return s

def solve_limit(num_str, den_str, x0_str):
    x = sp.Symbol('x')
    
    # 1. 解析传入的字符串为 SymPy 表达式
    num = sp.sympify(num_str.replace('^', '**'))
    den = sp.sympify(den_str.replace('^', '**'))
    x0 = sp.sympify(x0_str)

    # 2. 为了方便提取 (x - x0) 的次幂，我们做一个平移变换 t = x - x0
    t = sp.Symbol('t')
    num_t = sp.expand(num.subs(x, t + x0))
    den_t = sp.expand(den.subs(x, t + x0))

    # 3. 寻找分子分母中 t 的最低次幂
    def get_lowest_power(poly_t):
        if poly_t == 0: return float('inf')
        # 获取多项式的所有项，提取 t 的指数
        poly = sp.Poly(poly_t, t)
        if poly.is_zero: return float('inf')
        return min([monom[0] for monom in poly.monoms()])

    k_num = get_lowest_power(num_t)
    k_den = get_lowest_power(den_t)
    
    # 4. 约去的公共次幂
    k_cancel = min(k_num, k_den)

    # 5. 提取并约分
    num_rem_t = sp.simplify(num_t / (t**k_cancel))
    den_rem_t = sp.simplify(den_t / (t**k_cancel))

    # 6. 还原回 x 的表达式
    p_x = num_rem_t.subs(t, x - x0)
    q_x = den_rem_t.subs(t, x - x0)

    # 7. 判断极限是否发散 (即分母剩余的 t 的次数仍大于 0)
    is_divergent = bool(k_den > k_num)
    m_val = int(k_den - k_num) if is_divergent else 0
    k_val = int(k_cancel)

    # 8. 构造返回给 Lean 的 JSON 数据
    result = {
        "is_divergent": is_divergent,
        "p": sympy_to_lean(p_x),
        "q": sympy_to_lean(q_x),
        "k": k_val,
        "m": m_val
    }
    print(json.dumps(result))

if __name__ == "__main__":
    # 从命令行接收参数: python limit_oracle.py "(x^2-1)" "(x-1)" "1"
    solve_limit(sys.argv[1], sys.argv[2], sys.argv[3])
