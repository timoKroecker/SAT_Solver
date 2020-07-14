def isIn(x, array):
        for a in array:
            if(x == a):
                return True
        return False

def sort_literals(lit_list):
    changes_made = True
    while(changes_made):
        changes_made = False
        for i in range(lit_list.__len__() - 1):
            if(lit_list[i].to_string() > lit_list[i + 1].to_string()):
                backup = lit_list[i + 1]
                lit_list[i + 1] = lit_list[i]
                lit_list[i] = backup
                changes_made = True
    return lit_list

def clause_to_string(clause):
    string = ""
    for lit in clause:
        string = string + lit.to_string() + ", "
    return "{" + string[:-2] + "}"

def sort_clauses(clause_list):
    changes_made = True
    while(changes_made):
        changes_made = False
        for i in range(clause_list.__len__() - 1):
            if(clause_to_string(clause_list[i]) > clause_to_string(clause_list[i + 1])):
                backup = clause_list[i + 1]
                clause_list[i + 1] = clause_list[i]
                clause_list[i] = backup
                changes_made = True
    return clause_list

def klauselmenge_as_string(klauselmenge):
    menge = klauselmenge
    string_array = []
    for klaus in menge:
        string = "{"
        for lit in klaus:
            string = string + lit.to_string() + ", "
        if(string.__len__() == 1):
            string = string + "}"
        else:
            string = string[:-2] + "}"
        if(not isIn(string, string_array)):
            string_array.append(string)
    output_string = "{"
    for string in string_array:
        output_string = output_string + string + ", "
    return output_string[:-2] + "}"

def literal_is_in(lit, clause):
    for l in clause:
        if(lit.to_string() == l.to_string()):
            return True
    return False

def clause_is_in(cl, klm):
    for k in klm:
        if(clause_to_string(cl) == clause_to_string(k)):
            return True
    return False

def remove_tautologies(clause):
    for i in range(clause.__len__() - 1):
        for j in range(clause.__len__() - i - 1):
            if(j >= clause.__len__()):
                break
            if(clause[i].to_string()[1:] == clause[j + i + 1].to_string()):
                clause = clause[:j + i + 1] + clause[j + i + 2:]
                clause = clause[:i] + clause[i + 1:]
                clause = remove_tautologies(clause)
                break
    return clause

def get_resolvente(clause_a, clause_b):
    res = []
    for lit in clause_a:
        res.append(lit)
    for lit in clause_b:
        if(not literal_is_in(lit, res)):
            res.append(lit)
    res = sort_literals(res)
    changes_made = True
    while(changes_made):
        changes_made = False
        for i in range(res.__len__()):
            for j in range(res.__len__() - i - 1):
                k = j + i + 1
                if(res[i].to_string()[1:] == res[k].to_string()):
                    res.remove(res[i])
                    res.remove(res[k - 1])
                    changes_made = True
                    break
            if(changes_made):
                break
    if(res.__len__() < clause_a.__len__() + clause_b.__len__()):
        return res
    return None

def has_empty_clause(klm):
    for cl in klm:
        if(cl == []):
            return True
    return False

#--------------------------------------------------------------------------------------------------------------------------------------------
#-------------------------------------------------------------2. SAT Aufgabe (Blatt 8)-------------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------------------------------

def print_wahrheitstafel(formula):

    #--------------------Footnotes:
    #--------------------1: Falls formula eine Negation ist, ist right == None
    #--------------------2: Eliminierung von Redundanz
    #--------------------3: +4 wegen den vier Spaces, -5 wegen Laenge von "true " bzw "false"
    #--------------------4: Laenge von "|  a  |" == a.__len__() + 6

    atoms = formula.get_atoms()
    formula_len = formula.to_string().__len__()
    left_len = formula.left.to_string().__len__()
    width = formula_len + left_len + 19                                         #Nur wichtig für die Länge der Horizontal Linie (7x "|" + 12 Spaces == 19)
    if(formula.right != None):                                                  #Footnote 1
        right_len = formula.right.to_string().__len__()
        width = width + right_len	   
    zeilen = 2**atoms.__len__()

    for a in atoms:                                                             #Kopf
        print("|  " + a.name + "  |", end = "")
        width = width + 7                                                       #Footnote 4

    print("|", end = "")

    if(formula.left.__class__.__name__ == "Atom"):                              #Footnote 2
        width = width - 7                                                       #Footnote 4
    else:
        print("|  " + formula.left.to_string() + "  |", end = "")

    if(formula.right == None):                                                  #Footnote 1
        pass
    elif(formula.right.__class__.__name__ == "Atom"                             #Footnote 2
    or formula.left.to_string() == formula.right.to_string()):                  #Footnote 2
        width = width - right_len - 6                                           #Footnote 4
    else:
        print("|  " + formula.right.to_string() + "  |", end = "")

    print("|  " + formula.to_string() + "  |", end = "")
    

    print("")

    for i in range(width):                                                      #Horizontal Linie
        print("-", end="")

    print("")

    for i in range(zeilen):                                                     #Rumpf
        modul = zeilen                                                          #\begin{Belegungen fuer aktuelle Zeile setzen}
        obergrenze = zeilen / 2
        for a in atoms:
            if(i % modul < obergrenze):
                a.set_value(True)
            else:
                a.set_value(False)
            modul = modul / 2
            obergrenze = obergrenze / 2                                         #\end{Belegung fuer aktuelle Zeile setzen}

        for a in atoms:       
            print("|" + a.value_as_string() + "|", end = "")

        print("|", end = "")

        if(formula.left.__class__.__name__ != "Atom"):                          #Footnote 2
            print("|", end = "")                                                
            spaces_left = left_len - 1                                          #\begin{Zentrierung des boolean: linke Teilformel} Footnote 3
            for i in range(spaces_left // 2):
                print(" ", end = "")
            spaces_left = spaces_left - (spaces_left // 2)
            print(formula.left.value_as_string(), end = "")      
            for i in range(spaces_left):              
                print(" ", end = "")                                            #\end{Zentrierung des boolean: linke Teilformel}
            print("|", end = "")

        if(formula.right != None                                                #Footnote 1
        and formula.right.__class__.__name__ != "Atom"                          #Footnote 2
        and formula.left.to_string() != formula.right.to_string()):             #Footnote 2
            print("|", end = "")                                               
            spaces_left = right_len - 1                                         #\begin{Zentrierung des boolean: rechte Teilformel} Footnote 3
            for i in range(spaces_left // 2):
                print(" ", end = "")
            spaces_left = spaces_left - (spaces_left // 2)
            print(formula.right.value_as_string(), end = "")                        
            for i in range(spaces_left):
                print(" ", end = "")                                            #\end{Zentrierung des boolean: rechte Teilformel}
            print("|", end = "")

        print("|", end = "")                                                   
        spaces_left = formula_len - 1                                           #\begin{Zentrierung des boolean: volle Formel} Footnote 3
        for i in range(spaces_left // 2):                                     
            print(" ", end = "")                                                
        spaces_left = spaces_left - (spaces_left // 2)                         
        print(formula.value_as_string(), end = "")                        
        for i in range(spaces_left):
            print(" ", end = "")                                                #\end{Zentrierung des boolean: volle Formel}
        print("|", end = "")

        print("")

    print("")
    print("")

#--------------------------------------------------------------------------------------------------------------------------------------------
#---------------------------------------------------------------3. SAT Aufgabe (Blatt 9)-----------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------------------------------

def print_isDisjunctionOfLiterals(formula):
    print("DISJUNKTION VON LITERALEN?")
    if(formula.is_disjunction_of_literals()):
        print("     " + formula.to_string())
        print("     JA")
    else:
        print("     " + formula.to_string())
        print("     NEIN")

    return False

def print_KNF(formula):
    first_step = formula.remove_imps()
    second_step = first_step.nnf()
    third_step = second_step.knf()

    print("\n\nKOMMUTATIVE NORMALFORM")
    print("Im Folgenden wird die Formel " + formula.to_string() + " in die KNF übergeführt:\n")
    print("     Erster Schritt - Entfernung der Implikationen:")
    print("     " + first_step.to_string() + "\n")
    print("     Zweiter Schritt - Überführung in NNF:")
    print("     " + second_step.to_string() + "\n")
    print("     Dritter Schritt - Überführung in KNF:")
    print("     " + third_step.to_string() + "\n\n")

    return third_step

#--------------------------------------------------------------------------------------------------------------------------------------------
#---------------------------------------------------------------4. SAT Aufagbe (Blatt 10)----------------------------------------------------
#--------------------------------------------------------------------------------------------------------------------------------------------

def print_resolution(formula):
    #Vorbedingung: formula ist in KNF
    print("Resolution der Formel " + formula.to_string() + ":\n")
    klm = formula.get_klauselmenge()
    for j in range(klm.__len__()):
        klm[j] = remove_tautologies(klm[j])
    last_len = klm.__len__()
    i = 0

    print("     Res" + i.__str__() + " = " + klauselmenge_as_string(klm) + "\n")

    to_be_appended = []
    for j in range(klm.__len__() - 1):
        for k in range(klm.__len__() - j - 1):
            if(k + j + 1 >= klm.__len__()):
                break
            new_res = get_resolvente(klm[j], klm[k + j + 1])
            if(new_res != None and not clause_is_in(new_res, klm)):
                to_be_appended.append(new_res)
    for j in to_be_appended:
        klm.append(j)

    while(last_len != klm.__len__()):
        last_len = klm.__len__()
        i = i + 1
        print("     Res" + i.__str__() + " = " + klauselmenge_as_string(klm) + "\n")

        to_be_appended = []
        for j in range(klm.__len__() - 1):
            for k in range(klm.__len__() - j - 1):
                if(k + j + 1 >= klm.__len__()):
                    break
                new_res = get_resolvente(klm[j], klm[k + j + 1])
                if(new_res != None and not clause_is_in(new_res, klm)):
                    to_be_appended.append(new_res)
        for j in to_be_appended:
            klm.append(j)

    if(has_empty_clause(klm)):
        print("     Die leere Menge ist enthalten. \n\n\n")
    else:
        print("     Die leere Menge ist nicht enthalten. \n\n\n")

    #print(last_len)
    #print(klm.__len__())