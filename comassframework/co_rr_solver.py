#!/usr/bin/env python3
# vim: tabstop=8 expandtab shiftwidth=4 softtabstop=4

# Framework written by 
# Pascal Bongaertz
# Daniel Goßen
# Hendrik Willing

# Added by
# Stan Derksen
# Falco IJben
# Veerle van Winden
# OVERAL WAAR APPELTAART STAAT MOETEN WIJ WAT DOEN CTRL F DIE SHIT


"""
SYNOPSIS
    co_rr_solver [OPTION] [DIRECTORY]

DESCRIPTION
    All found recurrence relations in DIRECTORY that have filenames matching "comass??.txt"
    are inspected and a direct formula describing these recurrence relations is stored in the
    file "comass??-dir.txt". If DIRECTORY is omitted, the location of "co_rr_solver" is taken
    as directory.

    -v, --verbose
        print debugging information during execution of "co_rr_solver"
"""

import glob # Library for filename pattern-matching
import sympy as sy
from sympy.parsing.sympy_parser import parse_expr
from sympy import sympify, roots, solve, expand, factor
from sympy.abc import r, n
import sys # For access to the given argument
import os  # Gives access to current location of co_rr_solver


# Global variables:
next_symbolic_var_index = 0 # This variable indicates the next index for the p_x variable names needed for Theorem 6.
print_debug_information = False # This variable indicates whether debug information should be printed (this is read in using the command line argument list)

"""Print the given list line by line, each line started and ended with a quotation mark."""
def print_list(listing):
    for line in listing:
        print("\"" + line + "\"")

"""Print the dictionary element per element: First key, then ":" and value."""
def print_dict(dictionary):
    for key in dictionary:
        print(str(key) + ": " + str(dictionary[key]))

"""First checks if debug printing is allowed.
   Then checks the type of the input of the function.
   Then prints the input based on the type of input."""
def debug_print(debug_information):
    global print_debug_information
    if print_debug_information:
        if type(debug_information) == dict:
            print_dict(debug_information)
        elif type(debug_information) == list:
            print_list(debug_information)
        else:
            print(str(debug_information))

"""Determines for each line in lines:
    The x-value of s(x) and the corresponding y-value of s(x)=y.
    This is returned as dictionary where x is the integer-key and y the string-value."""
def det_init_conditions(lines):
    conditions = {}
    for line in lines:
        pos_s_bracket = line.find("s(") # Position of "s("
        start_index_nr = pos_s_bracket + 2 # First index of x-value
        pos_bracket_equal = line.find(")=", pos_s_bracket) # Position of ")="
        start_index_y = pos_bracket_equal + 2 # First position after the "=" symbol
        x_value = int(line[start_index_nr:pos_bracket_equal])
        y_value = line[start_index_y:]
        conditions[x_value] = y_value
    return conditions

"""Searches for the left begin of the term (beginning at start) and returns the first position belonging to the term, where the symbols are still
    counted as part of the term (may be handy for "+" and "-", but REMIND THIS if the symbols list also contains "*" and "/")..
    The begin of a new term is indicated with one of the symbols in the list "symbols", but only if there are no opened brackets at this position."""
def search_left_term_begin(equation, start, symbols):
    bracket_count = 0 # Indicating the number of opened bracket-scopes
    index = start
    while index >= 0:
        if equation[index] == ")":
            bracket_count += 1
        elif equation[index] == "(":
            bracket_count -= 1
        elif bracket_count == 0 and equation[index] in symbols:
            return index
        index -= 1
    return 0 # If we got until here the term starts at the begin of equation

"""Searches for the right end of the term (beginning at start) and returns the last position belonging to the term.
    The begin of a new term is indicated with one of the symbols in the list "symbols", but only if there are no opened brackets at this position."""
def search_right_term_end(equation, start, symbols):
    bracket_count = 0 # Indicating the number of opened bracket-scopes
    index = start
    while index < len(equation):
        if equation[index] == "(":
            bracket_count += 1
        elif equation[index] == ")":
            bracket_count -= 1
        elif bracket_count == 0 and equation[index] in symbols and index > 0:
            return index - 1
        index += 1
    return len(equation) - 1 # If we got until here the term ends at the end of equation

"""Determines and returns:
    1. The value of x in s(n-x) as integer, where pos_s should be the index of "s" in equation
    2. equation where "s(n-x)" is replaced by "1"."""
def recurrent_step_length(equation, pos_s):
    exclusive_end_pos = equation.find(")", pos_s)
    value = equation[pos_s + 4:exclusive_end_pos]
    equation = equation.replace("s(n-" + value + ")", "1") # Replace "s(n-x)" with "1"
    return int(value), equation


"""Determines and returns:
    1. A dictionary of the associated homogeneous recurrence relation in default form, where:
        -The integer-key is x of s(n-x) (thus without minus)
        -The string-value is y of y*s(n-x)
    2. A list of string-terms of F(n)."""
def analyze_recurrence_equation(equation):
    associated = {}
    f_n_list = []
    equation = equation[5:len(equation)] # Remove the "s(n)="-part
    pos_s = equation.find("s(n-") # First position of recurrent part
    while pos_s >= 0: # There is another recurrent s(n-x) part
        debug_print(equation)
        step_length, equation = recurrent_step_length(equation, pos_s) # Determines step length and replaces recurrent part with a "1"
        debug_print(step_length)
        left_pos = search_left_term_begin(equation, pos_s, ["+", "-"])
        right_pos = search_right_term_end(equation, pos_s, ["+", "-"])
        c_n = equation[left_pos:right_pos + 1] # Substring with both indexes inclusive
        debug_print("c_n "+ c_n)
        equation = equation.replace(c_n, "", 1) # Remove the actual c_n from the equation (only once)
        associated[step_length] = c_n # Add the recursive step length and factor to the dictionary
        pos_s = equation.find("s(n-") # First position of recurrent part (because other "s(n-"-part is already removed)

    # The rest of the equation, the part that does not satisfies the s(n- thingy, is the F(n) part. APPELTAART
    f_n_list = process_f_n_string(equation)

    return associated, f_n_list

def process_f_n_string(equation):
    if not equation:
        return []
    # To prevent false splitting, we first need to replace the content of brackets with 'appeltaart'
    appeltaart_counter = 1
    appeltaarten = {}
    left_index = equation.find("(")
    right_index = equation.find(")")
    result = []

    # Some magic to change some of the equation to appeltaart
    #TODO: dit gaat nog fout bij bijv: (1 * (2 -7)), nested brackets. maar fuck dat
    while(left_index != -1):
        appeltaart = equation[left_index:right_index+1]
        appeltaarten[appeltaart_counter] = appeltaart
        replacement = "appeltaart_" + str(appeltaart_counter) + ";"
        equation = equation.replace(appeltaart, replacement, 1)
        appeltaart_counter += 1

        left_index = equation.find("(")
        right_index = equation.find(")")

    # Split the string on the plusses without removing the plusses
    parts = ["+" + e for e in equation.split("+") if e]

    # Split the string on the minusses, and add them to the result list
    for part in parts:
        minusses = part.split("-")
        # First minus is actually a plus
        result.append(minusses[0])
        for x in range(1, len(minusses)):
            result.append(("-" + minusses[x]))


    # Some magic to change the appeltaart back to maths :(
    for x in range(0, len(result)):
        r = result[x]
        if "appeltaart" in r:
            index1 = r.find("_")
            index2 = r.find(";")
            number = r[index1+1:index2]
            result[x] = r.replace("appeltaart_"+number+";", appeltaarten[int(number)])

    return result



"""Reads in all lines of the file except the first, second and last one.
    The lines are returned as list of strings."""
def read_file(filename):
    lines = []
    with open(filename, "r") as input_file:
        for index, line in enumerate(input_file):
            if not (index in [0, 1]) and line != "];\n": # Filter out first and second row and the last that contains "];\n"
                lines.append(line.strip()) # Append and remove leading and closing whitspaces
    return lines

"""Goes through all rows except the last and delete the "," at the end.
    The result is returned (again as list of strings)."""
def clear_commas(lines):
    for index, line in enumerate(lines):
        if index < len(lines) - 1: # This is not the last line
            comma_pos = len(line) - 1 # The last index position where the "," stands
            lines[index] = line[:comma_pos]
    return lines

"""Deletes all remaining whitespace and converts "^" to "**".
    The result is returned (again as list of strings)."""
def fix_syntax(lines):
    for index, line in enumerate(lines):
        line = str.replace(line, " ", "")
        line = str.replace(line, "^", "**")
        lines[index] = line
    return lines

"""Finds a closed formula for a homogeneous recurrence relation.
    The return value is a string of the right side of the equation "s(n) = ..."""
def solve_homogeneous_equation(init_conditions, associated):
    print("The associated incomming variable", associated)
    # You have to implement this yourself! APPELTAART
    # 1: Rewrite the recurrence equation in default form  above do n-1 before n-2
    sorted_equation = rewrite_equation(associated)
    # 2: Determine the characteristic equation c_n already in associated
    characteristic_equation = determine_characteristic_equation(sorted_equation)
    # 3: Find the roots (sympy has a module roots() also gives multiplicities)
    poly_roots = find_roots(characteristic_equation)
    # 4: Find the general solution
    general_solution = find_general_solution(poly_roots)
    # 4.5: Format for finding alpha
    system = format_general_solution_for_determining_alphas(general_solution, init_conditions)
    # 5: use the initial conditions to determine the exact value of alpha.
    alphas = determine_alpha(init_conditions, system)
    result = replace_alphas_in_solution(general_solution, alphas)
    print('the ultimate result is: ' + result)

    return result

def rewrite_equation(equation):
    result = {}
    length = int(max(equation, key=int))
    for key in range(1, length+1):
        if key in equation:
            result[key] = equation[key]
        else:
            result[key] = "+0*1"
    print("sorted equation:", result)

    return result

def replace_alphas_in_solution(solution, alphas):
    if type(alphas) == type([]):
        alphas = alphas[0]
    for a in alphas.keys():
        solution = solution.replace(str(a), str(sy.nsimplify(alphas[a])))

    return solution


def determine_characteristic_equation(equation):
    result = {}
    k = len(equation)
    index = 0
    result[index] = "1*r**%s" % k
    k = k - 1
    index = index + 1
    for key in equation.keys():
        partial_eq = "%s*r**%s" % (equation[key].split("*")[0], k)

        #Hacky bugfix incoming
        partial_eq = list(partial_eq)
        if partial_eq[0] == '+':
            partial_eq[0] = '-'
            partial_eq = ''.join(partial_eq)
        elif partial_eq[0] == '-':
            partial_eq[0] = '+'
            partial_eq = ''.join(partial_eq)
        else:
            partial_eq = ''.join(partial_eq)
            partial_eq = '-' + partial_eq
            partial_eq = ''.join(partial_eq)

        result[index] = partial_eq
        k = k - 1
        index = index + 1

    print("characteristic equation:", result)

    return result


def find_roots(equation):
    poly_values = []
    for key, value in equation.items():
        # poly_values.append(float(value.split("*r")[0]))
        poly_values.append(parse_expr(value.split("*r")[0]))
    poly_roots = sy.roots(poly_values)
    print("roots:", poly_roots)


    return poly_roots


def find_general_solution(roots):
    result = "a_n = "
    k = 1
    for root in roots.keys():
        multiplicity = roots[root]
        if multiplicity == 1:
            result += "a_" + str(k) + " * (" + str(sy.nsimplify(root)) + ")**n +"
            k += 1
        else:
            for i in range(multiplicity):
                result += 'a_' + str(k) + ' * (' + str(sy.nsimplify(root)) + ')**n * n**' + str(i) + ' +'
                k += 1
    result = list(result)
    del result[-2:]
    result = ''.join(result)
    print('General solution: ' + result)
    return result


def format_general_solution_for_determining_alphas(general_solution, initial_conditions):
    system = []

    for n in initial_conditions.keys():
        general_solution_copy = general_solution
        s_n = str(initial_conditions[n])
        n = str(n)
        general_solution_copy = general_solution_copy.replace('*n','*'+n)
        general_solution_copy = general_solution_copy.replace('n*', n+'*')
        general_solution_copy = general_solution_copy[6:]
        general_solution_copy = general_solution_copy + ' - ' + s_n
        sy_exp = parse_expr(general_solution_copy)
        system.append(sy_exp)
    return system


def determine_alpha(init_conditions, system):
    result = sy.solve(system)
    print(result)

    return result

"""Finds a closed formula for a nonhomogeneous equation, where the nonhomogeneous part consists
    of a linear combination of constants, "r*n^x" with r a real number and x a positive natural number,
    and "r*s^n" with r and s being real numbers.
    The return value is a string of the right side of the equation "s(n) = ..."""
def solve_nonhomogeneous_equation(init_conditions, associated, f_n_list):
    v = 0
    # 1: Rewrite the recurrence equation in default form  above do n-1 before n-2
    sorted_equation = rewrite_equation(associated)
    # 2: Determine the characteristic equation c_n already in associated
    characteristic_equation = determine_characteristic_equation(sorted_equation)
    # 3: Find the roots (sympy has a module roots() also gives multiplicities)
    poly_roots = find_roots(characteristic_equation)
    # 4: Find the general solution
    general_solution = find_general_solution(poly_roots)
    # 5: Find a particular solution
    particular_solution = find_particular_solution(sorted_equation, f_n_list)
    print('particular_solution: ' + str(particular_solution))
    print('general_solution: ' + str(general_solution))
    # 6: plak shit aan elkaar
    solution = general_solution + ' + ' + particular_solution
    print('solution: ' + solution)
    # 7: laat sympy de shot oplossen
    system_of_eq = format_general_solution_for_determining_alphas(solution, init_conditions)
    print('sys of eq: ')
    print(system_of_eq)
    alphas = determine_alpha(init_conditions, system_of_eq)
    result = replace_alphas_in_solution(solution, alphas)
    print('the ultimate result is: ' + result)

    return result


def find_particular_solution(sorted_equation, f_n_list):

    A, B, C, D, E = sy.symbols('A B C D E')
    forms_dict = {'(A*n**4+B*n**3+C*n**2+D*n+E)':[A,B,C,D,E],
                  '(A*n**3+B*n**2+C*n+D)':[A,B,C,D],
                  '(A*n**2+B*n+C)':[A,B,C],
                  '(A*B**n+C)':[A,C],
                  '(A*B**n)':[A],
                  'A*n+B':[A,B],
                  'A':[A]}
    for form in forms_dict.keys():
        result = build_solution_form(form, sorted_equation, f_n_list,forms_dict[form])
        result = result[0]
        flag = False
        for k in result.keys():
            s = str(result[k])
            if 'A' in s or 'B' in s or 'C' in s or 'D' in s or 'E' in s:
                flag = True
        if not flag:
            print('Form is: ',form)
            print('Result is: ', result)

            for k in result.keys():
                form = form.replace(str(k), str(result[k]))
            print(form)

            return form

    return 'appeltaart'




def build_solution_form(form, sorted_equation, f_n_list, symbols):
    # WARNING works for only a single an_ variable
    # To demonstrate, i will use [an] = [an_(-2)] + [0.5*n**2 + 0.5*n] this is the odd nugget example from the slides.
    # Brackets indicate separate parts (to be used later in the documentation of this function)
    # We know the form is '(A*n**2+B*n+C)'
    b_val = 'appeltaart'
    if form == '(A*B**n+C)' or form == '(A*B**n)':
        b_val = 'B'
        for fn in f_n_list:
            if '**(n' in fn:
                # NOTE bugs if the base of the exponent is not at +10**(n-1) but is preceeded by another term
                b_val = fn[1:fn.find('**')]

        form = form.replace('B',b_val)
    eq = ''
    for k in sorted_equation.keys():
        # We add the coeficient to the equation
        current = sorted_equation[k] + '*'
        eq += current
        new_n = '(n-' + str(k) + ')'
        new_form = form.replace('n',new_n)
        eq += new_form
        eq += '+'
    # Remove the last +
    eq = eq[:-1]
    # The form of the equation will now be +0*1(A*n-1**2+B*n-1+C)1*1(A*n-2**2+B*n-2+C)
    # As an_(-1) = 0 and an_(-2) = 1
    # We combine the f_n_list to a single string to obtain F(n)
    f_n_final = '('
    for f_n in f_n_list:
        f_n_final += f_n
    f_n_final += ')'
    eq += '+1*'
    eq += f_n_final
    # We now have: +0*1(A*n-1**2+B*n-1+C)+1*1(A*n-2**2+B*n-2+C)++0.5*n**2+0.5*n
    # To set it to zero, we substract the form (which translates to a_n) from the equation
    eq += '-1*'
    eq += form
    # We now have '1(A*n**2+B*n+C)+0.5*n**2+0.5*n-(A*n**2+B*n+C)'
    # or with brackets: '[1(A*n**2+B*n+C)] + [0.5*n**2+0.5*n] - [(A*n**2+B*n+C)]'
    # You read this as 0 = 1(A*n**2+B*n+C)+0.5*n**2+0.5*n-(A*n**2+B*n+C)
    eq = parse_expr(eq)
    eq = sy.nsimplify(eq)
    result = sy.solve(eq, symbols, dict=True)
    if b_val != 'appeltaart':
        result[0]['B'] = b_val

    return result

"""Transforms the string equation, that is of the right side of the form "s(n) = ...",
    and wirtes it towards the file "filename", which also needs to contain the desired path."""
def write_output_to_file(filename, equation):
    nr_written_chars = 0
    with open(filename, "w") as output_file:
        nr_written_chars = output_file.write("sdir := n -> {0};\n".format(equation))
    debug_print("Wrote {0} characters to file {1}.".format(str(nr_written_chars), filename))

"""Reformats the for Python needed syntax of equations back to specified output format:
    - "**" is transformed back to "^";
    - "sqrt(...)" is transformed back to "(...)^(1/2)".
    The return value is a string of the modified equation."""
def reformat_equation(equation):
    equation = equation.replace("**", "^")
    pos_sqrt = equation.find("sqrt(")
    while pos_sqrt >= 0:
        pos_end = search_right_term_end(equation, pos_sqrt, ["+", "-", "*", "/"])
        equation = "{0}^(1/2){1}".format(equation[0:pos_end + 1], equation[pos_end + 1:])
        equation = equation.replace("sqrt", "", 1)
        pos_sqrt = equation.find("sqrt(")
    return equation

# Functions for determining type of F(n)


def is_linear(f_n):
    for f in f_n:
        if '*' in f:
            return True
    return False


def is_quadratic(f_n):
    for f in f_n:
        if '**2' in f:
            return True
    return False


def is_exponential(f_n):
    for f in f_n:
        if '**(n' in f:
            return True
    return False


def is_cubic(f_n):
    for f in f_n:
        if '**3' in f:
            return True
    return False


def is_to_the_fourth(f_n):
    for f in f_n:
        if '**4' in f:
            return True
    return False

# Begin of program:
if len(sys.argv) > 3:
    print("Error: Illegal number of arguments.")
else:
    path = str(os.path.dirname(os.path.abspath(__file__)))
    print_debug_information = True
    print(sys.argv)
    if len(sys.argv) > 1:
        argv_index = 1
        if "-v" in sys.argv:
            print_debug_information = True
            if len(sys.argv) > 2:
                argv_index = 2
        elif "--verbose" in sys.argv:
            print_debug_information = True
            if len(sys.argv) > 2:
                argv_index = 2
        if sys.argv[argv_index].find("/") != -1:
            path = sys.argv[argv_index]
    print(path)
    for filename in glob.glob(path + "/comass[0-9][0-9].txt"):
        print("File: "+filename)
        next_symbolic_var_index = 0 # Reset this index for every file
        debug_print("Beginning for file \"{0}\"".format(filename))
        lines = read_file(filename)
        lines = clear_commas(lines)
        lines = fix_syntax(lines)
        print("Len lines: " + str(len(lines)))
        debug_print(lines)
        # The following quick fix was done because some input files had two newlines at their end and the list "lines" thus may contain one empty line "" at the end
        tmp = len(lines)
        if lines[len(lines) - 1] == "":
            tmp -= 1
        init_conditions = det_init_conditions([lines[index] for index in range(1, tmp)]) # Determine initial conditions with all but the first line as input
        associated, f_n_list = analyze_recurrence_equation(lines[0])

        # Print debugging information:
        debug_print(filename)
        debug_print("Initial conditions:")
        debug_print(init_conditions)
        debug_print("Associated homogeneous recurrence relation:")
        debug_print(associated)
        debug_print("F(n):")
        debug_print(f_n_list)

        output_filename = filename.replace(".txt", "-dir.txt")
        resulting_equ = ""
        # Check if the equation is a homogeneous relation
        if not f_n_list: # The list is empty
            resulting_equ = solve_homogeneous_equation(init_conditions, associated)
        else:
            resulting_equ = solve_nonhomogeneous_equation(init_conditions, associated, f_n_list)
        resulting_equ = reformat_equation(str(sy.nsimplify(resulting_equ[6:])))
        write_output_to_file(output_filename, resulting_equ)

        debug_print("#################################\n")
    print("Program is completely executed. There are no more recurrence relations to compute.")
