import static_methods as stm

tt = "true "                                                                        #immer Laenge 5
ff = "false"                                                                        #immer Laenge 5

class Atom:
    def __init__(self, name):
        self.name = name
        self.value = None
        self.atoms = []
        self.atoms.append(self)

    def to_string(self):
        return self.name

    def get_value(self):
        return self.value

    def set_value(self, value):
        self.value = value

    def value_as_string(self):
        if(self.value == None):
            return "none "
        elif(self.value):
            return tt
        else:
            return ff

    def atoms_as_string(self):
        return self.name

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return True

    def remove_imps(self):
        return self

    def nnf(self):
        return self

    def knf(self):
        return self

    def get_literals(self):
        literals = []
        literals.append(self)
        return literals

    def get_klauselmenge(self):
        #Vorbedingung: Formel ist in KNF
        menge = []
        menge.append(self.get_literals())
        return menge


class Not:
    def __init__(self, p):
        self.left = p
        self.right = None
        self.atoms = []
        for a in p.get_atoms():
            self.atoms.append(a)

    def to_string(self):
        if(self.left.__class__.__name__ == "Atom"):
            return "!" + self.left.to_string()
        else:
            return "!(" + self.left.to_string() + ")"

    def get_value(self):
        return not self.left.get_value()

    def value_as_string(self):
        if(self.get_value()):
            return tt
        else:
            return ff

    def atoms_as_string(self):
        string = ""
        for a in self.atoms:
            if(string.__len__() > 0):
                string = string + ", " + a.name
            else:
                string = string + a.name
        return string

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return self.left.__class__.__name__ == "Atom"

    def remove_imps(self):
        return Not(self.left.remove_imps())

    def nnf(self):
        if(self.left.__class__.__name__ == "Atom"):
            return self
        elif(self.left.__class__.__name__ == "Not"):
            return self.left.left.nnf()                                                     #stimmt so!
        elif(self.left.__class__.__name__ == "And"):
            return Or(Not(self.left.left), Not(self.left.right)).nnf()                      #stimmt so!
        elif(self.left.__class__.__name__ == "Or"):
            return And(Not(self.left.left), Not(self.left.right)).nnf()                     #stimmt so!

    def knf(self):
        return self

    def get_literals(self):
        if(self.left.__class__.__name__ == "Atom"):
            literals = []
            literals.append(self)
            return literals
        else:
            return stm.sort_literals(self.left.get_literals())

    def get_klauselmenge(self):
        #Vorbedingung: Formel ist in KNF
        menge = []
        menge.append(self.get_literals())
        return menge
    

class And:
    def __init__(self, p, q):
        self.left = p
        self.right = q
        self.atoms = []
        for a in self.left.get_atoms():
            self.atoms.append(a)
        for a in self.right.get_atoms():
            if(not stm.isIn(a, self.atoms)):
                self.atoms.append(a)

    def to_string(self):
        if( self.left.__class__.__name__ == "Atom"
            or self.left.__class__.__name__ == "Not"
            or self.left.__class__.__name__ == "And"):
            left_string = self.left.to_string()
        else:
            left_string = "(" + self.left.to_string() + ")"

        if( self.right.__class__.__name__ == "Atom"
            or self.right.__class__.__name__ == "Not"
            or self.right.__class__.__name__ == "And"):
            right_string = self.right.to_string()
        else:
            right_string = "(" + self.right.to_string() + ")"
        
        return left_string + " /\\ " + right_string

    def get_value(self):
        return self.left.get_value() and self.right.get_value()

    def value_as_string(self):
        if self.get_value():
            return tt
        else:
            return ff

    def atoms_as_string(self):
        string = ""
        for a in self.atoms:
            if(string.__len__() > 0):
                string = string + ", " + a.name
            else:
                string = string + a.name
        return string

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return False

    def remove_imps(self):
        return And(self.left.remove_imps(), self.right.remove_imps())

    def nnf(self):
        return And(self.left.nnf(), self.right.nnf())

    def knf(self):
        return And(self.left.knf(), self.right.knf())

    def get_literals(self):
        lit = self.left.get_literals()
        for l in self.right.get_literals():
            if(not stm.isIn(l, lit)):
                lit.append(l)
        lit = stm.sort_literals(lit)
        return lit

    def get_klauselmenge(self):
        #Vorbedingung: Formel ist in KNF
        menge = self.left.get_klauselmenge()
        for k in self.right.get_klauselmenge():
            menge.append(k)
        menge = stm.sort_clauses(menge)
        return menge


class Or:
    def __init__(self, p, q):
        self.left = p
        self.right = q
        self.atoms = []
        for a in self.left.get_atoms():
            self.atoms.append(a)
        for a in self.right.get_atoms():
            if(not stm.isIn(a, self.atoms)):
                self.atoms.append(a)

    def to_string(self):
        if( self.left.__class__.__name__ == "Imp"
            or self.left.__class__.__name__ == "BiImp"):
            left_string = "(" + self.left.to_string() + ")"
        else:
            left_string = self.left.to_string()

        if( self.left.__class__.__name__ == "Imp"
            or self.right.__class__.__name__ == "BiImp"):
            right_string = "(" + self.right.to_string() + ")"
        else:
            right_string = self.right.to_string()

        return left_string + " \\/ " + right_string

    def get_value(self):
        return self.left.get_value() or self.right.get_value()

    def value_as_string(self):
        if self.get_value():
            return tt
        else:
            return ff

    def atoms_as_string(self):
        string = ""
        for a in self.atoms:
            if(string.__len__() > 0):
                string = string + ", " + a.name
            else:
                string = string + a.name
        return string

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return self.left.is_disjunction_of_literals() and self.right.is_disjunction_of_literals()

    def remove_imps(self):
        return Or(self.left.remove_imps(), self.right.remove_imps())

    def nnf(self):
        return Or(self.left.nnf(), self.right.nnf())

    def knf(self):
        if(self.is_disjunction_of_literals()):
            return self
        elif(self.left.__class__.__name__ == "And"):
            return And(Or(self.left.left, self.right).knf(), Or(self.left.right, self.right).knf())
        elif(self.right.__class__.__name__ == "And"):
            return And(Or(self.left, self.right.left).knf(), Or(self.left, self.right.right).knf())
        else:
            return Or(self.left.knf(), self.right.knf()).knf()

    def get_literals(self):
        lit = self.left.get_literals()
        for l in self.right.get_literals():
            if(not stm.isIn(l, lit)):
                lit.append(l)
        lit = stm.sort_literals(lit)
        return lit

    def get_klauselmenge(self):
        #Vorbedingung: Formel ist in KNF
        if(self.is_disjunction_of_literals()):
            menge = []
            menge.append(self.get_literals())
            return menge
        else:
            menge = self.left.get_klauselmenge()
            for k in self.right.get_klauselmenge():
                menge.append(k)
            menge = stm.sort_clauses(menge)
            return menge
        

class Imp:
    def __init__(self, p, q):
        self.left = p
        self.right = q
        self.atoms = []
        for a in self.left.get_atoms():
            self.atoms.append(a)
        for a in self.right.get_atoms():
            if(not stm.isIn(a, self.atoms)):
                self.atoms.append(a)

    def to_string(self):
        return "(" + self.left.to_string() + " -> " + self.right.to_string() + ")"

    def get_value(self):
        return (not self.left.get_value()) or self.right.get_value()

    def value_as_string(self):
        if self.get_value():
            return tt
        else:
            return ff

    def atoms_as_string(self):
        string = ""
        for a in self.atoms:
            if(string.__len__() > 0):
                string = string + ", " + a.name
            else:
                string = string + a.name
        return string

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return False

    def remove_imps(self):
        return Or(Not(self.left.remove_imps()), self.right.remove_imps())


class BiImp:
    def __init__(self, p, q):
        self.left = p
        self.right = q
        self.atoms = []
        for a in self.left.get_atoms():
            self.atoms.append(a)
        for a in self.right.get_atoms():
            if(not stm.isIn(a, self.atoms)):
                self.atoms.append(a)

    def to_string(self):
        return "(" + self.left.to_string() + " <-> " + self.right.to_string() + ")"

    def get_value(self):
        return ((not self.left.get_value()) or self.right.get_value()) and ((not self.right.get_value()) or self.left.get_value())

    def value_as_string(self):
        if self.get_value():
            return tt
        else:
            return ff

    def atoms_as_string(self):
        string = ""
        for a in self.atoms:
            if(string.__len__() > 0):
                string = string + ", " + a.name
            else:
                string = string + a.name
        return string

    def get_atoms(self):
        return self.atoms

    def is_disjunction_of_literals(self):
        return False

    def remove_imps(self):
        return And(Or(Not(self.left.remove_imps()), self.right.remove_imps()), Or(Not(self.right.remove_imps()), self.left.remove_imps()))