from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO

def cond_inv_to_tex(cond_inv):
    smtlib = "\n".join([
        cond_inv, 
        "(declare-fun s () (_ BitVec 4))",
        "(declare-fun t () (_ BitVec 4))",
        "(assert (= (_ bv0 4) (" + "inv" + " s t) " + " ))",
        "(check-sat)"
        ])
    buf = cStringIO(smtlib)
    parser = SmtLibParser()
    script_in = parser.get_script(buf)
    buf_out = cStringIO()
    script_in.serialize(buf_out)
    f_in = script_in.get_last_formula()
    print(f_in)

def axiom_to_tex(axiom)

cond_inv_to_tex("(define-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4) s)")
cond_inv_to_tex("(define-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4) (bvnot #b0000))")
cond_inv_to_tex("(define-fun inv ((s (_ BitVec 4)) (t (_ BitVec 4))) (_ BitVec 4) (bvand t #b1000))")
