from statements import *
import static_methods as stm


#--------------------------------------------------------------------------------------------------------------------------------------------
#---------------------------------------------------------------Tests------------------------------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------------------------------

#1. SAT Aufgabe (Blatt 7)
print("\n\n-----------------------------------------------------------------------------------------------------")
print("                                              BLATT 7")
print("-----------------------------------------------------------------------------------------------------\n")

print("Diese Teilaufgabe ist zu trivial, um Zeit mit Tests zu verschwenden.")

#2. SAT Aufgabe (Blatt 8)
print("\n\n-----------------------------------------------------------------------------------------------------")
print("                                              BLATT 8")
print("-----------------------------------------------------------------------------------------------------\n")
print("WAHRHEITSTAFEL TESTS\n")

p = Atom("p")
q = Atom("q")
r = Atom("r")
p_or_q = Or(p, q)
nq = Not(q)
r_or_nq = Or(r, nq)
p_or_q_and_r_or_nq = And(p_or_q, r_or_nq)
stm.print_wahrheitstafel(p_or_q_and_r_or_nq)

t = Atom("t")
not_t = Not(t)
mofucka = BiImp(not_t, p_or_q_and_r_or_nq)
stm.print_wahrheitstafel(mofucka)
print("AAA                                                AAA")
print("|||Tabellengröße passt sich der Anzahl der Atome an|||\n\n")

not_p = Not(p)
not_p_and_q = And(not_p, q)
crash = Not(not_p_and_q)
stm.print_wahrheitstafel(crash)
print("AAA                                                                        AAA")
print("|||Formeln mit rechter Teilformel = None (hier Negation) funktionieren auch|||\n\n")

p_biimp_p = BiImp(p, p)
stm.print_wahrheitstafel(p_biimp_p)
print("AAA                                                             AAA")
print("|||Linke und rechte Teilformel werden wegelassen, wenn redundant|||\n\n")


print("\nHILBERT-KALKÜL\n")

A = Atom("A")
B = Atom("B")
C = Atom("C")

BfA = Imp(B, A)                         #Ax1
Ax1 = Imp(A, BfA)
stm.print_wahrheitstafel(Ax1)

BfC = Imp(B, C)                         #Ax2
AfBfC = Imp(A, BfC)
AfB = Imp(A, B)
AfC = Imp(A, C)
AfBfAfC = Imp(AfB, AfC)
Ax2 = Imp(AfBfC, AfBfAfC)
stm.print_wahrheitstafel(Ax2)

nA = Not(A)                             #Ax3
nB = Not(B)
nAfnB = Imp(nA, nB)
Ax3 = Imp(nAfnB, BfA)
stm.print_wahrheitstafel(Ax3)


#3.SAT Aufabe (Blatt 9)
print("\n\n-----------------------------------------------------------------------------------------------------")
print("                                              BLATT 9")
print("-----------------------------------------------------------------------------------------------------\n")

one = Or(p_or_q, r_or_nq)
two = Or(one, not_p)
three = Not(two)
stm.print_isDisjunctionOfLiterals(one)
stm.print_isDisjunctionOfLiterals(two)
stm.print_isDisjunctionOfLiterals(three)
stm.print_isDisjunctionOfLiterals(Ax1)
stm.print_isDisjunctionOfLiterals(p_biimp_p)
stm.print_isDisjunctionOfLiterals(p)

Ax3_knf = stm.print_KNF(Ax3)
stm.print_KNF(And(Ax1, Ax3))
stm.print_KNF(Not(And(Ax1, Ax3)))
var = stm.print_KNF(Ax2)


#4.SAT Aufabe (Blatt 10)
print("\n\n-----------------------------------------------------------------------------------------------------")
print("                                              BLATT 10")
print("-----------------------------------------------------------------------------------------------------\n")

print("SORTIERUNG\n")

print("Sortierte Klauselmenge von " + Ax3_knf.to_string() + ":")
print("     " + stm.klauselmenge_as_string(Ax3_knf.get_klauselmenge()) + "\n\n")

print("Sortierte Klauselmenge von " + var.to_string() + ":")
print("     " + stm.klauselmenge_as_string(var.get_klauselmenge()) + "\n\n")

print("RESOLUTION\n")

x = Atom("x")
y = Atom("y")
ny = Not(y)
x_or_y = Or(x, y)
x_or_ny = Or(x, ny)
new_knf = And(x_or_y, x_or_ny)

stm.print_resolution(new_knf)

stm.print_resolution(Ax3_knf)

print("AAA                                              AAA")
print("||| Tautologien werden schon bei Res0 eliminiert |||\n\n\n")

not_r = Not(r)
s = Atom("s")
not_s = Not(s)
not_q = Not(q)
een = Or(Or(not_p, not_r), s)
drie = Or(Or(not_p, not_q), r)
vier = Or(Or(not_p, q), s)
vijf = And(een, not_s)
zes = And(drie, vier)
zeven = And(vijf, zes)
acht = And(zeven, p)

print("Beispiel - Blatt 7 Aufgabe 3:\n")
stm.print_resolution(acht)

print("AAA                                                               AAA")
print("|||Übersichtlichkeit bei zu langen Formeln ist nur bedingt gewährt|||\n\n\n")