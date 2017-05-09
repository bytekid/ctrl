
import re
import sys
from pyparsing import Word, alphas, ParseException, Literal, CaselessLiteral \
, Combine, Optional, nums, Or, Forward, ZeroOrMore, StringEnd, alphanums \
, CharsNotIn, OneOrMore, LineStart, LineEnd, srange

# globals
funapp_modifiers = set()
logical_terms = {}

def id(x):
  return x

def const(c):
  return (lambda x: c)

# util
def tohex(val, nbits):
  return hex((val + (1 << nbits)) % (1 << nbits))

# expressions
class Expr:
  def __init__(self):
    pass

  def toString(self):
    return ""

  def visit(self, vvar, vfun, vbinop, rec):
    return self


class Skip(Expr):
  def __init__(self):
    pass

  def toString(self):
    return "skip"


class Constant(Expr):
  def __init__(self, c):
    self.val = c

  def toString(self):
    return self.val


class Num(Expr):
  def __init__(self, c):
    self.val = c

  def padTo(x,n):
    if len(x) >= 4:
      return x 
    else:
      return padTo("0" + x, n)

  def toString(self):
    h = tohex(int(self.val),32)[2:]
    while len(h) < 8: # 32 bit for now
      h = "0" + h
    return "#x" + h


class Ident(Expr):
  def __init__(self, c):
    self.val = c

  def toString(self):
    return self.val

  def visit(self, vvar, vfun, vbinop, rec):
    return vvar(self)


class Unop(Expr):
  replace_name = { "-" : "neg", "!" : "not" }

  def __init__(self, op, v):
    assert(isinstance(v, Expr))
    rep_op = self.replace_name.get(op)
    self.op = rep_op if rep_op else op
    self.val = v

  def toString(self):
    return self.op + "(" + self.val.toString() + ")"

  def visit(self, vvar, vfun, vbinop, rec):
    return Unop(self.op, self.val.visit(vvar, vfun, vbinop, rec))


class Binop(Expr):
  replace_name = { "&&" : "/\\", "||" : "\\/", "==" : "=", \
                   "+" : "+i", "-" : "-i", "*" : "*i",
                   "<=" : "i<=", ">=" : "i>=", "<" : "i<", ">" : "i>"}

  def __init__(self, op, a, b):
    assert isinstance(a, Expr)
    assert(isinstance(b, Expr))
    self.op = op
    self.val1 = a
    self.val2 = b

  def toString(self):
    rep = self.replace_name.get(self.op)
    op = rep if rep else self.op
    return "(" + self.val1.toString() + " " + op + " " + \
		       self.val2.toString() + ")"

  def visit(self, vvar, vfun, vbinop, rec):
    if rec(self):
      b = Binop(self.op, self.val1.visit(vvar, vfun, vbinop, rec), \
                self.val2.visit(vvar, vfun, vbinop, rec))
      return vbinop(b)
    else:
      return vbinop(self)


class FunApp(Expr):
  replace_name = { "and" : "And",  "xor" : "Xor", "not" : "Not", "or" : "Or", \
                   "true" : "True", "false" : "False" }
  # hasOneUse tends to have non-logical terms as arguments
  # since we can not faithfully encode it anyway, suppress for now
  suppress_args = { "hasOneUse" : True }

  def __init__(self, name, is_term):
    rep = self.replace_name.get(name)
    self.name =  rep if rep else name
    self.args = []
    self.is_term = is_term

  def setArgs(self, args):
    self.args = args

  def getName(self):
    return self.name

  def isTerm(self):
    return self.is_term

  def setMod(self, m):
    global funapp_modifiers
    mm = tuple([self.name, m[1:], len(self.args)])
    funapp_modifiers.add(mm)
    self.name += m

  def toString(self):
    suppress = self.suppress_args.get(self.name)
    args = "" if len(self.args) == 0 or suppress else "(" + \
           reduce(lambda s, e: s + ("" if len(s) == 0 else ", ") + \
                               e.toString(), self.args, "") + ")"
    return self.name + args
  
  def visit(self, vvar, vfun, vbinop, rec):
    if rec(self):
      rs = reduce(lambda rs, a: rs + [a.visit(vvar, vfun, vbinop, rec)], self.args,[])
      f = FunApp(self.name, self.is_term)
      f.setArgs(rs)
      return vfun(f)
    else:
      return vfun(self)


class Rule:
  def __init__(self, name, lhs, rhs, cond):
    self.name = name
    self.lhs = lhs
    self.rhs = rhs
    self.cond = cond

  def toString(self):
    pre = "  [ " + self.cond.toString() + "] " if self.cond else ""
    return "  " + self.lhs.toString() + " -> " + self.rhs.toString() + pre
  
  def show(self):
    print("Rule " + self.name + ": " + self.toString())

def syms(term):
  fs = []
  if isinstance(term, FunApp):
    fs.insert(0, term.name)
    fs = reduce(lambda acc, arg: acc + syms(arg), term.args, fs)
  return fs

def symbols(rules):
  fs = []
  for r in rules:
    fs += syms(r.lhs) + syms(r.rhs)
  return list(set(fs))

def printLCTRS(rules):
  print("THEORY bitvectors;")
  print("LOGIC QF_UFBV;")
  print("SOLVER external;")
  syms = symbols(rules)
  print("SIGNATURE " + reduce(lambda s, e: s + e + ", ", syms, "") + \
        " !BITVECTOR;")
  print("\nRULES")
  for r in rules:
    print("  " + r.toString() + ";")
  print("\nNON-STANDARD IRREGULAR")
  print("\nQUERY termination")

lctrs = []
variables = {}

def pushExpr(e):
  #print(e)
  return [e]

def pushAgain(str, loc, toks):
  return toks

def pushExpr0(create):
  return (lambda toks: pushExpr(create(toks[0])))

def pushExpr1(create):
  return (lambda toks: pushExpr(create(toks[0], toks[1])))

  replace_name = { "abs" : "absbv", "xor" : "xxor", "not" : "nnot", "true" : "ttrue", \
                   "false" : "ffalse" }
def pushExpr2(create):
  return (lambda toks: pushExpr(create(toks[1], toks[0], toks[2])))

def pushFun(toks, is_term):
  name = toks[0]
  assert isinstance(name, basestring)
  f = FunApp(name, is_term)
  if len(toks) > 1:
    args = toks[len(toks) - 1]
    f.setArgs(args)
    #for a in args:
    #  if is_term and ((isinstance(a, FunApp) and not a.isTerm()) or isinstance(a, Binop)):
    #    print "argument "+ a.toString() + " is alien!" + toks['pre']
  if len(toks) == 3:
    f.setMod(toks[1])
  return [f]

def pushLogicFun(toks):
  return pushFun(toks, False)

def pushTermFun(toks):
  return pushFun(toks, True)

def pushXFun(toks):
  name = toks[0]
  f = FunApp(name, False)
  f.setArgs([toks[1]])
  f.setMod(toks[2])
  return [f]

def makeArgs(toks):
  return [toks]

def assignVar(toks):
  global variables
  id = toks[0].toString()
  variables[id] = toks[1]
  return [{"var": id, "expr": toks[1]}]

def mkSide(toks):
  return [toks[len(toks) - 1]]

def clearVars():
  variables.clear()

def replaceIdent(id):
  assert(isinstance(id, Ident))
  global variables
  val = variables.get(id.toString())
  if val:
    return val
  return id

def replaceTheorySymsPre(funapp):
  # types are not checked as this function is only applied to precondition
  replace_names = [ "abs", "ashr", "log2", "lshr", "sext", "trunc", "zext" ]
  #
  n = funapp.getName()
  if n in replace_names:
    f = FunApp(n + "_th", funapp.isTerm())
    f.setArgs(funapp.args)
    return f
  else:
    return funapp

def mkIdent(toks):
  global variables
  val = variables.get(toks[0])
  if val:
    return val
  return Ident(toks[0])

def replaceBinOp(e):
  assert(isinstance(e, Binop))
  global logical_terms
  if logical_terms.get(e.toString()):
    return logical_terms[e.toString()][0]
  else:
    x = Ident("CL" + str(len(logical_terms)))
    logical_terms[e.toString()] = [x,e]
    #print("replace " + e.toString() + " by " + x.toString())
    return x

def addRule(toks):
  global lctrs
  global logical_terms
  logical_terms = {}
  lhs = toks["lhs"].pop()
  rhs = toks["rhs"].pop()
  lexp = lhs["expr"].visit(id, id, replaceBinOp, lambda e: isinstance(e,FunApp))
  rexp = rhs["expr"].visit(id, id, replaceBinOp, lambda e: isinstance(e,FunApp))
  # concat additional preconditions
  pre = toks.get("pre") if toks.get("pre") else None
  for key in logical_terms:
    eq = logical_terms[key]
    p = Binop("==", eq[1], eq[0])
    pre = p if pre == None else Binop("&&", p, pre)
  #
  if pre != None:
    # (1) substitute temp vars in precondition
    pre = pre.visit(replaceIdent, id, id, const(True))
    # (2) replace lshr, ashr by theory counterparts in precondition
    pre = pre.visit(id, replaceTheorySymsPre, id, const(True))
  #
  rule = Rule(toks["name"], lexp, rexp, pre if pre else None)
  if lhs["var"] != rhs["var"]:
    print("ERROR: " + lhs["var"] + " == " + rhs["var"])
  lctrs = lctrs + [rule]
  return [rule]

def mkLit(s):
	return Literal(s)

def mkMod(toks):
	return reduce(lambda s, t: s + "_" + t, toks, "")

# define grammar
name = (LineStart() + Literal("Name:")).suppress()
pre = Literal("Pre:").suppress()
num = Combine(Optional(Literal("-")) + Word(nums))
assign = Literal("=").suppress()
constant = Combine(Literal("C") + Optional(Word(nums)))
skip = Literal("skip")
to = Literal("to").suppress()
percent = Literal("%").suppress()
ident = Combine(percent + Word(alphanums))
funName = Word(srange("[a-zA-Z]"), alphanums)
lpar  = Literal( "(" ).suppress()
rpar  = Literal( ")" ).suppress()
comma  = Literal( "," ).suppress()
# theory expression
unops = ["~", "-"]
lBvUnop = Or(mkLit(s) for s in unops)
unops = ["!"]
lUnop = Or(mkLit(s) for s in unops)
binops = ["&", "|", "^", ">>", "u>>", "<<", "+", "-", "*", "/", "/u", "%", "%u"]
lBvBinop = Or(mkLit(s) for s in binops)
binops = ["&&", "||"]
lBinop = Or(mkLit(s) for s in binops)
cmps = ["==", "!=", "<", ">", "u<", "u>", "<=", ">=", "u<=", "u>="]
lCmp = Or(mkLit(s) for s in cmps)
funs = ["abs", "computeKnownZeroBits", "countLeadingZeros","countTrailingZeros", \
        "log2", "lshr", \
        "max", "umax", "width"]
xfuns = ["sext", "trunc", "zext", "ZExtOrTrunc"]
lBvFun = Or(mkLit(s) for s in funs + xfuns)
xFun = Or(mkLit(s) for s in xfuns)
funs = ["equivalentAddressValues", "hasOneUse", "isPowerOf2", \
        "isPowerOf2OrZero", \
        "isSafeToLoadUnconditionally", "isShiftedMask", "isSignBit", \
        "MaskedValueIsZero", \
        "WillNotOverflowSignedAdd",  "WillNotOverflowUnsignedAdd",  \
        "WillNotOverflowSignedSub", "WillNotOverflowUnsignedSub", \
        "WillNotOverflowSignedMul", "WillNotOverflowUnsignedMul", \
        "WillNotOverflowSignedShl", "WillNotOverflowUnsignedShl"]
lBoolFun = Or(mkLit(s) for s in funs)
mods = ["eq", "exact", "ne", "sge", "sgt", "sle", "slt", "uge", "ugt", "ule", "ult", \
        "nuw", "nsw", "Ty"]
sizeMod = Combine(Literal("i") + Word(nums))

lBvExpr = Forward()
lBvExprFactor = Forward()
lBvArgs = (ZeroOrMore(lBvExpr + comma) + lBvExpr).setParseAction(makeArgs)
lBvExprFactor << (constant.setParseAction(pushExpr0(lambda c: Constant(c))) |\
                 ident.setParseAction(mkIdent) | \
                 num.setParseAction(pushExpr0(lambda c: Num(c))) | \
                 (lBvFun + lpar + lBvArgs + rpar).setParseAction(pushLogicFun)|\
						     (lBvUnop + lBvExprFactor).setParseAction(pushExpr1( \
                   lambda op, arg: Unop(op, arg))) | \
                 (lpar + lBvExpr + rpar).setParseAction(pushAgain))
lBvExpr << ((lBvExprFactor + lBvBinop + lBvExpr).setParseAction(pushExpr2( \
              lambda op, arg1, arg2: Binop(op, arg1, arg2))) | \
            lBvExprFactor)

lBoolExpr = Forward()
lBoolExprFactor = Forward()
lBoolExprFactor << ((lpar + lBoolExpr + rpar).setParseAction(pushAgain) | \
                    (lBoolFun + lpar + lBvArgs + rpar).setParseAction(pushLogicFun)|\
                    (lUnop + lBoolExprFactor).setParseAction(pushExpr1( \
                       lambda op, arg: Unop(op, arg))) | \
                    (lBvExpr + lCmp + lBvExpr).setParseAction(pushExpr2( \
                       lambda op, arg1, arg2: Binop(op, arg1, arg2))))
						  
lBoolExpr << ((lBoolExprFactor + lBinop + lBoolExpr).setParseAction(pushExpr2( \
                lambda op, arg1, arg2: Binop(op, arg1, arg2))) | \
              lBoolExprFactor)

tBase = (lBvExpr |\
         Word(srange("[a-z]"), alphanums).setParseAction(pushTermFun))
tArgs = (ZeroOrMore(tBase + comma) + tBase).setParseAction(makeArgs)
tMod = OneOrMore(Or(mkLit(s) for s in mods) ^ sizeMod).setParseAction(mkMod)
tExpr = (lBvExpr | \
         (xFun  + tBase + to + sizeMod).setParseAction(pushXFun) | \
         (funName + Optional(tMod) + Optional(tArgs))\
           .setParseAction(pushTermFun))
var = Combine(percent + Word(alphanums)).setParseAction(pushExpr0( \
        lambda i: Ident(i)))

comment = Combine(Literal(";") + CharsNotIn("\n") + LineEnd()).suppress()
comments = ZeroOrMore(comment).suppress()
lineend = (LineEnd() + comments).suppress()
tVarDef = (var + assign + tExpr + Optional(comment)).setParseAction(assignVar)
side = OneOrMore(tVarDef).setParseAction(mkSide)
nameLine = name + CharsNotIn("\n").setResultsName("name") + \
           lineend.setParseAction(clearVars)
preLine = (pre + lBoolExpr.setResultsName("pre") + (lineend | comment))
rule = (nameLine + \
        Optional(preLine) + \
        side.setResultsName("lhs") + \
        Literal("=>") + \
        side.setResultsName("rhs")).setParseAction(addRule)
rules = OneOrMore(rule + comments)

def testPre(s):
  print("testPre: " + s)
  try:
    r = preLine.parseString(s)
    print("  " + r['pre'][0].toString())
  except Exception as exc:
    print("{}: {}".format(type(exc).__name__, exc))

def testVar(s):
  print("testVar: " + s)
  try:
    variables = {}
    r = tVarDef.parseString(s)
    print("  " + r[0]["var"].toString() + ": " + r[0]["expr"].toString())
  except Exception as exc:
    print("{}: {}".format(type(exc).__name__, exc))

def testRule(s):
  print("testRule: ")
  try:
    clearVars()
    r = rule.parseString(s)[0]
    r.show()
  except Exception as exc:
    print("{}: {}".format(type(exc).__name__, exc))

def testAllPre():
  testPre("Pre: C1 < C2")
  testPre("Pre: 1 < 24")
  testPre("Pre: (C1 u> C2)")
  testPre("Pre: C < (1)")
  testPre("Pre: !(C != 1)")
  testPre("Pre: C < (1 & 3)")
  testPre("Pre: C < 1 && C == 1 << 3")
  testPre("Pre: C12 == C5 + 3")
  testPre("Pre: isPowerOf2(C)")
  testPre("Pre: C1 != width(C1) - 1")
  testPre("Pre: (1<<C1) % C2 == 0 && C1 != width(C1)-1")
  testPre("Pre: (1<<C1) %u C2 == 0")
  testPre("Pre: C u>= (1<<(width(C)-1))")
  testPre("Pre: WillNotOverflowUnsignedShl(C2, C1)")
  testPre("Pre: MaskedValueIsZero(%Op0, 1<<(width(%Op0)-1)) && isPowerOf2(C)")
  testPre("Pre: MaskedValueIsZero(%X, (-1 u>> (width(C2)-C2)) << (width(C1)-C1))")
  testPre("Pre: zext(C+C2) >= width(C)")
  testPre("Pre: equivalentAddressValues(%p1, %p2)")
  testPre("Pre: hasOneUse(%ptr) && hasOneUse(%a)")
  testPre("Pre: C1 == ~C2")
  testPre("Pre: isPowerOf2(C1) && isPowerOf2(C2) && log2(C2) < log2(C1)")
  testPre("Pre: (C2 == sext(C+1))")
  testPre("Pre: C2 == C-1 && !isSignBit(C)")
  testPre("Pre: C0 == max(0, log2(C3-C2) - log2(C))")
  testPre("Pre: -C2 ^ -C1 == (C3-C2) ^ (C3-C1) && abs(C1-C2) u> C3")

def testAllVar():
  testVar("%r = add %x, %yz")
  testVar("%r = select false, %sum, %dif")
  testVar("%nota = xor %a, -1")
  testVar("%c = icmp ne %lhs, 0")
  testVar("%v = shl %v0, max(0, log2(C3-C2) - log2(C))")
  testVar("%newand = and %A, ~(C1^C2)")

def testAllRule():
  testRule("Name: AndOrXor:1146-2 \n\
    Pre: MaskedValueIsZero(%op0RHS, ~C) \n\
    %op0 = or %op0LHS, %op0RHS \n\
    %r = and %op0, C \n\
      => \n\
    %newLHS = and %op0LHS, C \n\
    %r = or %newLHS, %op0RHS")
  testRule("Name: AndOrXor:1207 \n\
    %a = and %x, C1 \n\
    %op0 = trunc %a \n\
    %r = and %op0, C2 \n\
      => \n\
    %newcast = trunc %x \n\
    %r = and %newcast, trunc(C1) & C2")
  testRule("Name: AndOrXor:1593 \n \
    Pre: isPowerOf2(%K1) && isPowerOf2(%K2) \n \
    %a1 = and %A, %K1 \n\
    %a2 = and %A, %K2 \n\
    %cmp1 = icmp eq %a1, 0 \n\
    %cmp2 = icmp eq %a2, 0 \n\
    %r = or %cmp1, %cmp2 \n\
      => \n\
    %mask = or %K1, %K2 \n\
    %masked = and %A, %mask \n\
    %r = icmp ne %masked, %mask")
  testRule("Name: AddSub:1063 \n \n\
    Pre: countTrailingZeros(C1) == 0 && C1 == C2+1 \n \n\
    %Y = and %Z, C2 \n\
    %LHS = xor %Y, C1 \n\
    %r = add %LHS, %RHS \n\
      => \n\
    %or = or %Z, ~C2 \n\
    %r = sub %RHS, %or")
  testRule("Name: AddSub:1156-3 \n \n\
    %a = add nuw %b, %b \n\
      => \n\
    %a = shl nuw %b, 1")
  testRule("Name: Select:465 \n \
    Pre: isPowerOf2(C1) && isPowerOf2(C2) && log2(C2) >= log2(C1) \n \
    %and = and %X, C1 \n\
    %c = icmp eq %and, 0 \n\
    %F = or i11 %Y, C2 \n\
    %r = select %c, %Y, %F \n\
      => \n\
    %v = ZExtOrTrunc %and \n\
    %v2 = shl %v, log2(C2)-log2(C1) \n\
    %r = or %v2, %Y")
  testRule("Name: Select:523 \n \
    Pre: (C2 == sext(C+1)) && C != (1<<(width(%x)-1))-1 \n \
    %c = icmp sgt %x, C \n\
    %X = sext %x to i15 \n\
    %r = select %c, %X, C2 \n\
      => \n\
    %c2 = icmp slt %X, C2 \n\
    %r = select %c2, C2, %X")
  testRule("Name: Select:762 \n\
    Pre: isPowerOf2(C) && isPowerOf2(C2-C3) && log2(C) < width(C2) \n \
    %lhs = and %Op, C \n\
    %c = icmp eq %lhs, 0 \n\
    %s = select %c, C2, C3 \n\
      => \n\
    %v0 = ZExtOrTrunc %lhs to i11 \n\
    %v = shl %v0, max(0, log2(C2-C3) - log2(C)) \n\
    %v2 = lshr %v, max(0, log2(C) - log2(C2-C3)) \n\
    %x = xor %v2, C2-C3 \n\
    %s = add %x, C3")
  testRule("Name: AddSub:1040 \n \
    Pre: C2 == ~C1 \n \
    %Y = or %Z, C2 \n\
    %X = xor %Y, C1 \n\
    %LHS = add %X, 1 \n\
    %r = add %LHS, %RHS ; blahblah\n\
      => \n\
    %and = and %Z, C1 \n\
    %r = sub %RHS, %and ; my blah")
  testRule("Name: AndOrXor:246 \n \
    Pre: hasOneUse(%op) && C2 & lshr(-1, C1) == C2 \n\
    %op = ashr %X, C1 \n\
    %r = and %op, C2 \n\
    => \n\
    %op  = lshr %X, C1 \n\
    %r = and %op, C2")

def test():
  testAllPre()
  testAllVar()
  testAllRule()

def parse(s):
  rs = rules.parseString(s)
  #print("Read " + str(len(rs)) + " rules")
  #for r in rs:
  #  print("  " + r.toString())
  return rs


def getModRule(m):
  xs = []
  for i in range(0,m[2]):
    xs = xs + [Ident("X" + str(i))]
  l = FunApp(m[0] + "_" + m[1], True)
  l.setArgs(xs)
  r = FunApp(m[0], True)
  r.setArgs(xs)
  return Rule("",l,r,None)

def getModRules(lctrs):
  global funapp_modifiers
  funapp_modifiers = list(funapp_modifiers)
  return reduce(lambda rs, m: rs + [getModRule(m)], funapp_modifiers, [])  

def main():
  global lctrs
  if len(sys.argv) < 2:
    print("Usage: transform.py <rules.opt>")
    return
  llvm_input = sys.argv[1]
  #print("reading " + llvm_input)
  with open(llvm_input) as file:
    data = file.read()
    res = parse(data)
    mod_rules = getModRules(lctrs)
    printLCTRS(lctrs + mod_rules)

def test2():
  testRule("Name: Select:523 \n \
    Pre: C != width(%C) \n \
    %c = icmp sgt %x, C \n\
    %X = sext %x to i15 \n\
    %r = select %c, %X, C2 \n\
      => \n\
    %c2 = icmp slt %X, C2 \n\
    %r = select %c2, C2, %X")

if __name__ == "__main__": main()