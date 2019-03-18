import utils
import sys
import os
import utils

#pow_rec_def = "(define-fun-rec pow2 ((b Int)) Int (ite (<= b 0) 1 (* 2 (pow2 (- b 1)))))"
pow_dec = "(declare-fun pow2 (Int) Int)"

extract_definitions = [
        "(define-fun bitof ((k Int) (l Int) (a Int)) Int (mod (div a (pow2 l)) 2))",
        "(define-fun int_all_but_msb ((k Int) (a Int)) Int (mod a (pow2 (- k 1))))"
        ]

and_helper = "(define-fun intand_helper ((a Int) (b Int)) Int (ite (and (= a 1) (= b 1) ) 1 0))"
#and_rec_def = "(define-fun-rec intand ((k Int) (a Int) (b Int)) Int (ite (<= k 1) (intand_helper (lsb k a) (lsb k b)) (+ (intand (- k 1) a b) (* (pow2 (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))"
and_dec = "(declare-fun intand (Int Int Int) Int)"

or_helper = "(define-fun intor_helper ((a Int) (b Int)) Int (ite (and (= a 0) (= b 0) ) 0 1))"
#or_rec_def = "(define-fun-rec intor ((k Int) (a Int) (b Int)) Int (ite (<= k 1) (intor_helper (lsb k a) (lsb k b)) (+ (intor (- k 1) a b) (* (pow2 (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))"
or_dec = "(declare-fun intor (Int Int Int) Int)"

xor_helper = "(define-fun intxor_helper ((a Int) (b Int)) Int (ite (or (and (= a 0) (=  b 1)) (and (= a 1) (= b 0))) 1 0))"
#xor_rec_def = "(define-fun-rec intxor ((k Int) (a Int) (b Int)) Int (ite (<= k 1) (intxor_helper (lsb k a) (lsb k b)) (+ (intxor (- k 1) a b) (* (pow2 (- k 1)) (intxor_helper (bitof k (- k 1) a) (bitof k (- k 1) b))))))"
xor_dec = "(declare-fun intxor (Int Int Int) Int)"

shared = [
"(define-fun intmax ((k Int)) Int (- (pow2 k) 1))",
"(define-fun intmin ((k Int)) Int 0)",
"(define-fun in_range ((k Int) (x Int)) Bool (and (>= x 0) (<= x (intmax k))))",
"(define-fun intudivtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) (- (pow2 k) 1) (div a b) ))",
"(define-fun intmodtotal ((k Int) (a Int) (b Int)) Int (ite (= b 0) a (mod a b)))",
"(define-fun intneg ((k Int) (a Int)) Int (intmodtotal k (- (pow2 k) a) (pow2 k)))",
"(define-fun intnot ((k Int) (a Int)) Int (- (intmax k) a))",
"(define-fun intmins ((k Int)) Int (pow2 (- k 1)))",
"(define-fun intmaxs ((k Int)) Int (intnot k (intmins k)))",
"(define-fun intshl ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a (pow2 b)) (pow2 k)))",
"(define-fun intlshr ((k Int) (a Int) (b Int)) Int (intmodtotal k (intudivtotal k a (pow2 b)) (pow2 k)))",
"(define-fun intashr ((k Int) (a Int) (b Int) ) Int (ite (= (bitof k (- k 1) a) 0) (intlshr k a b) (intnot k (intlshr k (intnot k a) b))))",
"(define-fun intconcat ((k Int) (m Int) (a Int) (b Int)) Int (+ (* a (pow2 m)) b))",
"(define-fun intadd ((k Int) (a Int) (b Int) ) Int (intmodtotal k (+ a b) (pow2 k)))",
"(define-fun intmul ((k Int) (a Int) (b Int)) Int (intmodtotal k (* a b) (pow2 k)))",
"(define-fun intsub ((k Int) (a Int) (b Int)) Int (intadd k a (intneg k b)))",
"(define-fun unsigned_to_signed ((k Int) (x Int)) Int (- (* 2 (int_all_but_msb k x)) x))",
"(define-fun intslt ((k Int) (a Int) (b Int)) Bool (< (unsigned_to_signed k a) (unsigned_to_signed k b)) )",
"(define-fun intsgt ((k Int) (a Int) (b Int)) Bool (> (unsigned_to_signed k a) (unsigned_to_signed k b)) )",
"(define-fun intsle ((k Int) (a Int) (b Int)) Bool (<= (unsigned_to_signed k a) (unsigned_to_signed k b)) )",
"(define-fun intsge ((k Int) (a Int) (b Int)) Bool (>= (unsigned_to_signed k a) (unsigned_to_signed k b)) )"
        ]

qf_partial_combined_shared_axioms = ["(define-fun pow2_base_cases () Bool (and (= (pow2 0) 1) (= (pow2 1) 2) (= (pow2 2) 4) (= (pow2 3) 8) ) )"]
full_combined_shared_axioms = [
"(define-fun pow2_ind_def () Bool (and (= (pow2 0) 1) (forall ((i Int)) (!(=> (> i 0) (= (pow2 i) (* (pow2 (- i 1)) 2))) :pattern ((instantiate_me i))) )))",
"(define-fun and_ind_def ((k Int)) Bool (forall ((a Int) (b Int)) (!(=> (and (> k 0) (in_range k a) (in_range k b)) (= (intand k a b) (+ (ite (> k 1) (intand (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intand_helper (bitof k (- k 1) a) (bitof k (- k 1) b)))))) :pattern ((instantiate_me a) (instantiate_me b))) ))",
"(define-fun or_ind_def ((k Int)) Bool (forall ((a Int) (b Int))  (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intor k a b) (+ (ite (> k 1) (intor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intor_helper (bitof k (- k 1) a) (bitof k (- k 1) b)))))) :pattern ((instantiate_me a) (instantiate_me b))) ))",
"(define-fun xor_ind_def ((k Int)) Bool (forall ((a Int) (b Int))  (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intxor k a b) (+ (ite (> k 1) (intxor (- k 1) (int_all_but_msb k a) (int_all_but_msb k b)) 0) (* (pow2 (- k 1)) (intxor_helper (bitof k (- k 1) a) (bitof k (- k 1) b)))))) :pattern ((instantiate_me a) (instantiate_me b))) ))"
        ]

partial_combined_shared_axioms = [
";pow2 properties",
"(define-fun pow2_weak_monotinicity () Bool (forall ((i Int) (j Int)) (=> (and (>= i 0) (>= j 0) ) (=> (<= i j) (<= (pow2 i) (pow2 j))) )))",
"(define-fun pow2_strong_monotinicity () Bool (forall ((i Int) (j Int)) (=> (and (>= i 0) (>= j 0) ) (=> (< i j) (< (pow2 i) (pow2 j))) ) ) )",
"(define-fun pow2_modular_power () Bool (forall ((i Int) (j Int) (x Int)) (! (=> (and (>= i 0) (>= j 0) (>= x 0) (distinct (mod (* x (pow2 i)) (pow2 j)) 0)) (< i j) ) :pattern ((instantiate_me i) (instantiate_me j) (instantiate_me x))) ) )",
"(define-fun pow2_never_even () Bool (forall ((k Int) (x Int)) (! (=> (and (>= k 1) (>= x 0)) (distinct (- (pow2 k) 1) (* 2 x)) ) :pattern ((instantiate_me k) (instantiate_me x))) ) )",
"(define-fun pow2_always_positive () Bool (forall ((k Int)) (! (=> (>= k 0) (>= (pow2 k) 1) ) :pattern ((instantiate_me k))) ) )",
"(define-fun pow2_div_zero () Bool (forall ((k Int)) (! (=> (>= k 0) (= (div k (pow2 k)) 0 ) ) :pattern ((instantiate_me k))) ) )",
"(define-fun pow2_properties () Bool (and pow2_base_cases pow2_weak_monotinicity pow2_strong_monotinicity pow2_modular_power pow2_never_even pow2_always_positive pow2_div_zero ) )",

";and properties",
"(define-fun and_max1 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k a (intmax k)) a)) :pattern ((instantiate_me a))) ))",
"(define-fun and_max2 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k 0 a) 0   )) :pattern ((instantiate_me a))) ))",
"(define-fun and_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intand k a a) a)) :pattern ((instantiate_me a))) ))",
"(define-fun rule_of_contradiction ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a))  (= (intand k (intnot k a) a) 0 )) :pattern ((instantiate_me a))) ))",
"(define-fun and_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intand k a b) (intand k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))",
"(define-fun and_difference1 ((k Int)) Bool (forall ((a Int) (b Int) (c Int)) (! (=> (and (distinct a b) (> k 0) (in_range k a) (in_range k b) (in_range k c) ) (or (distinct (intand k a c) b) (distinct (intand k b c) a))) :pattern ((instantiate_me a) (instantiate_me b) (instantiate_me c))) ))",
"(define-fun and_ranges ((k Int)) Bool (forall ((a Int) (b Int)) (!(and (=> (and (> k 0) (in_range k a ) (in_range k b ) ) (and (in_range k (intand k a b)) (<= (intand k a b) a) (<= (intand k a b) b) ) )) :pattern ((instantiate_me a) (instantiate_me b) )) ))",
"(define-fun and_properties ((k Int)) Bool (and (and_max1 k) (and_max2 k) (and_ide k) (rule_of_contradiction k) (and_sym k) (and_difference1 k) (and_ranges k) ))",
";or properties",
"(define-fun or_max1 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a (intmax k)) (intmax k))) :pattern ((instantiate_me a))) ))",
"(define-fun or_max2 ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a 0) a)) :pattern ((instantiate_me a)) )))",
"(define-fun or_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intor k a a) a)) :pattern ((instantiate_me a))) ))",
"(define-fun excluded_middle ((k Int)) Bool (forall ((a Int)) (!(=> (and (> k 0) (in_range k a)) (and (= (intor k (intnot k a) a) (intmax k)) (= (intor k a (intnot k a)) (intmax k))  )) :pattern ((instantiate_me a)) )))",
"(define-fun or_difference1 ((k Int)) Bool (forall ((a Int) (b Int) (c Int)) (! (=> (and (distinct a b) (> k 0) (in_range k a) (in_range k b) (in_range k c) ) (or (distinct (intor k a c) b) (distinct (intor k b c) a))) :pattern ((instantiate_me a) (instantiate_me b) (instantiate_me c))) ))",
"(define-fun or_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intor k a b) (intor k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))",
"(define-fun or_ranges ((k Int)) Bool (forall ((a Int) (b Int)) (!(and (=> (and (> k 0) (in_range k a) (in_range k b) ) (and (in_range k (intor k a b)) (>= (intor k a b) a) (>= (intor k a b) b) ) )) :pattern ((instantiate_me a) (instantiate_me b))) ))",
"(define-fun or_properties ((k Int)) Bool (and (or_max1 k) (or_max2 k) (or_ide k) (excluded_middle k) (or_sym k) (or_difference1 k) (or_ranges k) ))",
";xor properties",
"(define-fun xor_ide ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a) ) (= (intxor k a a) 0)) :pattern ((instantiate_me a))) ))",
"(define-fun xor_flip ((k Int)) Bool (forall ((a Int)) (! (=> (and (> k 0) (in_range k a)) (= (intxor k a (intnot k a)) (intmax k))) :pattern ((instantiate_me a))) ))",
"(define-fun xor_sym ((k Int)) Bool (forall ((a Int) (b Int)) (! (=> (and (> k 0) (in_range k a) (in_range k b)) (= (intxor k a b) (intxor k b a))) :pattern ((instantiate_me a) (instantiate_me b)))))",
"(define-fun xor_ranges ((k Int)) Bool (forall ((a Int) (b Int)) (!(and (=> (and (> k 0) (in_range k a) (in_range k b) ) (in_range k (intxor k a b)) )) :pattern ((instantiate_me a) (instantiate_me b))) ))",
"(define-fun xor_properties ((k Int)) Bool (and (xor_ide k) (xor_flip k) (xor_sym k) (xor_ranges k) ))"
        ]

axioms = { 
#            "rec": [
#            "(define-fun pow2_ax () Bool true)",
#            "(define-fun and_ax ((k Int)) Bool true)",
#            "(define-fun or_ax ((k Int)) Bool true)",
#            "(define-fun xor_ax ((k Int)) Bool true)"
#            ],
            "full": [
            ";full axioms",
            "(define-fun pow2_ax () Bool pow2_ind_def)",
            "(define-fun and_ax ((k Int)) Bool (and_ind_def k))",
            "(define-fun or_ax ((k Int)) Bool (or_ind_def k))",
            "(define-fun xor_ax ((k Int)) Bool (xor_ind_def k))"
            ],
            "partial": [
            ";partial axioms",
            "(define-fun pow2_ax () Bool pow2_properties)",
            "(define-fun and_ax ((k Int)) Bool (and_properties k))",
            "(define-fun or_ax ((k Int)) Bool (or_properties k))",
            "(define-fun xor_ax ((k Int)) Bool (xor_properties k))"
            ],
            "combined": [
            ";combined axioms",
            "(define-fun pow2_ax () Bool (and pow2_ind_def pow2_properties))",
            "(define-fun and_ax ((k Int)) Bool (and (and_ind_def k) (and_properties k)))",
            "(define-fun or_ax ((k Int)) Bool (and (or_ind_def k) (or_properties k)))",
            "(define-fun xor_ax ((k Int)) Bool (and (xor_ind_def k) (xor_properties k)))"
            ],
            "qf": [
            ";qf axioms",
            "(define-fun pow2_ax () Bool base_cases)",
            "(define-fun and_ax ((k Int)) Bool true)",
            "(define-fun or_ax ((k Int)) Bool true)",
            "(define-fun xor_ax ((k Int)) Bool true)"
            ]
        }

instantiate_me_line = "(declare-fun instantiate_me (Int) Bool)"

templates = {
#    "rec": "\n".join(
#        [pow_rec_def] + extract_definitions + [and_helper, and_rec_def, or_helper, or_rec_def, xor_helper, xor_rec_def] + 
#        shared + 
#        axioms["rec"]),
    "full": "\n".join(
        [instantiate_me_line, pow_dec] + [and_dec, or_dec, xor_dec] + extract_definitions + [and_helper, or_helper, xor_helper] +
        shared + 
        full_combined_shared_axioms +
        axioms["full"]
        ),
    "partial": "\n".join(
        [instantiate_me_line, pow_dec] + [and_dec, or_dec, xor_dec] + extract_definitions + [and_helper, or_helper, xor_helper] +
        shared + 
        qf_partial_combined_shared_axioms + 
        partial_combined_shared_axioms + 
        axioms["partial"]
        ),
    "combined": "\n".join(
        [instantiate_me_line, pow_dec] + [and_dec, or_dec, xor_dec] + extract_definitions + [and_helper, or_helper, xor_helper] +
        shared + 
        qf_partial_combined_shared_axioms + 
        full_combined_shared_axioms + 
        partial_combined_shared_axioms + 
        axioms["combined"]
        ),
    "qf": "\n".join(
        [pow_dec] + [and_dec, or_dec, xor_dec] + extract_definitions + 
        shared + 
        qf_partial_combined_shared_axioms + 
        axioms["qf"]
        )
    }

def main(templates_dir, with_patterns):
    if not with_patterns:
        remove_patterns()
    for key in templates.keys():
        f = open(templates_dir + "/" + key + ".smt2", "w")
        f.write(templates[key])

def remove_patterns():
    for template_name in templates.keys():
        templates[template_name] = remove_patterns_from(templates[template_name])

def remove_patterns_from(template):
    bang = template.find("!")
    while bang != -1:
        lpar_before_bang = template[:bang].rfind("(")
        matching_rpar = utils.find_parens(template)[lpar_before_bang]
        colon = bang + template[bang:].find(":")
        template = template[:lpar_before_bang] + \
                    template[bang + 1 : colon] + \
                    template[matching_rpar + 1:]
        bang = template.find("!")
    #remove instantiate me
    lines = template.splitlines()
    lines = [l for l in lines if "instantiate_me" not in l]
    template = "\n".join(lines)
    return template


if __name__ == "__main__":
    if len(sys.argv) < 2:
        print('arg1: templates dir\n')
        print('arg2: includes patterns? yes/no (optional)\n')
        exit(1)
    templates_dir = sys.argv[1]
    with_patterns = True
    if len(sys.argv) == 3:
        if sys.argv[2] == "no":
            with_patterns = False
        else:
            assert(sys.argv[2] == "yes")
    main(templates_dir, with_patterns)
