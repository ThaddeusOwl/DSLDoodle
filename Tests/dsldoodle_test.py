# Importing the libraries
import ply.lex as lex
import ply.yacc as yacc
import flet as ft
from automata.fa.nfa import NFA
import graphviz
from graphviz import Digraph
import re
import sys
import io
from datetime import datetime


# ======================
# Model
# ======================

# Global Variables
# old_out = sys.stdout
build_counter = 0
ast_timestamp_string = ""
timestamp_str = ""
new_namespace = {}
type_to_value = {}
value_to_type = {}
lex_counter = 0
sym_table = []
sem_errors = []
sem_visual_removed = True



def traverse_ast_for_semantics(ast_node, assign_token, symbol_token):
    """
    Recursively traverse the abstract syntax tree (AST) to perform semantic checks.
    
    Specifically, it checks for:
    1. Variable re-declaration.
    2. Variable usage before declaration.
    
    Parameters:
    - ast_node (tuple or None): A node in the AST, represented as a tuple.
    - assign_token (str): Token type that represents an assignment operator in the language.
    - symbol_token (str): Token type that represents a variable or symbol in the language.
    """
    
    if ast_node is None or not isinstance(ast_node, tuple):
        return

    for i, elem in enumerate(ast_node): 
        if isinstance(elem, tuple):
            traverse_ast_for_semantics(elem, assign_token, symbol_token)
        else:
            if value_to_type.get(elem) == symbol_token: 
                if elem in sym_table:
                    if i > 0 and ast_node[i-1] == assign_token:
                        sem_errors.append([elem, "Variable has already been defined"])
                else:
                    if i > 0 and ast_node[i-1] == assign_token:
                        sym_table.append(elem)
                    else:
                        sem_errors.append([ast_node[i], "Variable used before being defined"])  

def generate_nfa(token_defs):
    """
    Generate a Python code string that defines a Non-deterministic Finite Automaton (NFA)
    for a given set of token definitions. The generated code can be executed to visualize 
    the NFA using the automata-lib library.
    
    Parameters:
    - token_defs (dict): A dictionary where keys are token names and values are regular expressions 
                         representing the token.

    Returns:
    - str: A string containing Python code to generate and visualize the NFA.
    """
    # Define the NFA attributes
    states = {'Start'}
    input_symbols = set()
    transitions = {'Start': {}}
    final_states = set()

    # Process each regular expression
    for name, regex in token_defs.items():
        final_states.add(name)
        states.add(name)
        current_state = 'Start'
        
        i = 0
        while i < len(regex):
            # Check for character class
            match_char_class = re.match(r'\[(.+?)\]', regex[i:])
            if match_char_class:
                char_class = match_char_class.group(1)  # Match without brackets
                i += len(match_char_class.group(0))
            elif regex[i:].startswith('\\') and len(regex[i:]) > 1:
                char_class = regex[i:i+2]
                i += 2
            else:
                char_class = regex[i]
                i += 1

            char_read_state = f"{char_class}_Read"
            states.add(char_read_state)
            
            if len(char_class) > 1 and char_class.startswith('\\'):
                char_class = char_class[1]

            # Escape backslashes for string representation
            char_class = char_class.replace("\\", "\\\\")
            
            input_symbols.add(char_class)
            if char_class not in transitions[current_state]:
                transitions[current_state][char_class] = set()
            transitions[current_state][char_class].add(char_read_state)

            transitions[char_read_state] = {}

            # Handle quantifiers
            if i < len(regex) and regex[i] in ['+', '*', '?']:
                quantifier = regex[i]
                i += 1
                if quantifier == '+':
                    transitions[char_read_state][char_class] = {char_read_state}
                elif quantifier == '*':
                    transitions[char_read_state][char_class] = {char_read_state}
                    transitions[char_read_state][''] = {current_state, name}
                    transitions[current_state][''] = {name}
                elif quantifier == '?':
                    if '' not in transitions[current_state]:
                        transitions[current_state][''] = set()
                    transitions[current_state][''].add(char_read_state)
                
            current_state = char_read_state

        transitions[current_state][''] = {name}
        

    states_str = ', '.join(f'"{sta}"' for sta in states)
    input_symbols_str = ', '.join(f'"{sym}"' for sym in input_symbols)
    transitions_str = ',\n        '.join(f"'{state}': {trans}" for state, trans in transitions.items())
    final_states_str = ', '.join(f"'{state}'" for state in final_states)

    # Generate the final string without backslashes in the f-string
    nfa_str = f"""nfa = NFA(
    states={{ {states_str} }},
    input_symbols={{ {input_symbols_str} }},
    transitions={{
        {transitions_str}
    }},
    initial_state='Start',
    final_states={{ {final_states_str} }}
)

dot = graphviz.Digraph()

for state in nfa.states:
    if state in nfa.final_states:
        dot.node(state, shape='doublecircle')
    else:
        dot.node(state)

dot.node('', style='invisible')
dot.edge('', nfa.initial_state)

for from_state, transitions in nfa.transitions.items():
    for input_symbol, to_states in transitions.items():
        for to_state in to_states:
            dot.edge(from_state, to_state, label=input_symbol)

nfafilename = f'nfa_{timestamp_str}'
#nfafilename = "nfa"

dot.render(nfafilename, format='png')
"""
    
    return nfa_str

def get_patterns_from_module(namespace):
    """
    Extract token patterns from a namespace, following the convention:
    - Token names should start with 't_'.
    - Direct string assignments or function docstrings are considered as patterns.
    - 't_error' is excluded.
    
    Parameters:
    - namespace (dict): The namespace containing token definitions.
    
    Returns:
    - dict: A dictionary with token names (without the 't_' prefix) as keys 
            and their patterns as values.
    """
    
    patterns = {}
    for name, value in namespace.items():
        if name.startswith('t_') and name != 't_error':
            if isinstance(value, str):  # for direct assignments
                patterns[name[2:]] = value
            else:  # for function-based patterns
                patterns[name[2:]] = value.__doc__
    
    return patterns

def visualize_ast(ast, output_file='ast_tree'):
    """
    Visualize an Abstract Syntax Tree (AST) represented as nested tuples.
    
    Parameters:
    - ast (tuple): The AST represented as nested tuples.
    - output_file (str): The name of the output file (without extension).

    Outputs:
    - PNG file: A graphical representation of the AST.
    """
    dot = Digraph(comment='AST for the code')
    
    counter = [0]  

    def add_node(parent, child_label):
        counter[0] += 1
        child = 'node' + str(counter[0])
        dot.node(child, child_label)
        if parent:
            dot.edge(parent, child)
        return child

    def build_tree(node, parent=None):
        
        if type(node) is tuple:
            if type(node[0]) is tuple:
                for child in node:
                    build_tree(child, parent)
            else:
                parent = add_node(parent, node[0])
                for child in node[1:]:
                    build_tree(child, parent)
        else:
            add_node(parent, node)

    root = 'root'
    dot.node(root, 'Program')
    build_tree(ast, root)
    dot.render(output_file, format="png")

def get_lex_table(lexer):
    """
    Generate a table visualization of the tokens produced by the lexer.
    
    Parameters:
    - lexer: An iterable lexer object that produces token objects with 'type' and 'value' attributes.
    
    Returns:
    - ft.DataTable: A table visualization with columns "Token Type" and "Token Value".
    """    
    rows = []
    
    print("Lexer Token Types and Values:")
    for token in lexer:
        value_to_type[token.value] = token.type # Populate Lexer Value Dictionary
        type_to_value[token.type] = token.value # Populate Lexer Type Dictionary
        print(token.type + " - " + token.value)
        row = ft.DataRow(
            cells=[
                ft.DataCell(ft.Text(token.type)),
                ft.DataCell(ft.Text(token.value))
            ]
        )
        rows.append(row)

    # Create the table
    table = ft.DataTable(
        columns=[
            ft.DataColumn(ft.Text("Token Type")),
            ft.DataColumn(ft.Text("Token Value"))
        ],
        rows=rows, border=ft.border.all(3,color = "BLACK"), vertical_lines=ft.border.BorderSide(3, color = "BLACK"),
            horizontal_lines=ft.border.BorderSide(3, color = "BLACK")
    )    
    print()
    return table

def get_symbol_table(array):
    """
    Generate a table visualization for a list of symbols (variables).
    
    Parameters:
    - array (list of str): List of symbols or variable names.
    
    Returns:
    - ft.DataTable: A table visualization of the provided symbols.
    """    
    columns = [ft.DataColumn(ft.Text("Symbol Table (Variables)"))]
    
    rows = []
    for item in array:
        cells = [ft.DataCell(ft.Text(item))]
        row = ft.DataRow(cells=cells)
        rows.append(row)
        
    return ft.DataTable(columns=columns, rows=rows, border=ft.border.all(3,color = "BLACK"), vertical_lines=ft.border.BorderSide(3, color = "BLACK"),
            horizontal_lines=ft.border.BorderSide(3, color = "BLACK"))

def get_sem_error_table(array):
    """
    Generate a table visualization for a list of semantic errors.
    
    Parameters:
    - array (list of tuples): List of semantic errors as tuples (variable, error message).
    
    Returns:
    - ft.DataTable: A table visualization of the provided errors.
    """    
    # Define columns
    columns = [
        ft.DataColumn(ft.Text("Variable")),
        ft.DataColumn(ft.Text("Error")),
    ]
    
    # Create rows
    rows = []
    for row_array in array:
        symbol, error = row_array
        cells = [
            ft.DataCell(ft.Text(symbol)),
            ft.DataCell(ft.Text(str(error))),
        ]
        row = ft.DataRow(cells=cells)
        rows.append(row)
    
    return ft.DataTable(columns=columns, rows=rows, border=ft.border.all(3,color = "BLACK"), vertical_lines=ft.border.BorderSide(3, color = "BLACK"),
            horizontal_lines=ft.border.BorderSide(3, color = "BLACK"))



def main(page: ft.Page):   
    
    """
    Contains the Controllers for the Model and the View for the user.
    
    Parameters:
    - page (ft.Page): The main page object where UI components are added.
    """

    # ======================
    # Controllers
    # ======================

    def build_button_click(e):
        
        """
        Event handler for the "build" button click.
        
        Processes the language rules, generates an NFA visualization, 
        and updates the UI with the results.
        
        Parameters:
        - e: Event object (not used in the function but typically provided by event handlers).
        """

        global build_counter
        new_namespace
        build_counter = build_counter + 1
       
        rules_string = rules.value
        rules_string = rules_string.replace("¨", "\"")
        rules_string = rules_string.replace("´", "\'")

        build_out = io.StringIO()        
        # sys.stdout= build_out 

        # Generate a timestamp string for uniquely naming files
        global timestamp_str
        timestamp_str = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")

        if build_counter > 1:
            new_namespace.clear()

        exec(rules_string, globals())
        exec(rules_string, new_namespace)
        
        patterns = get_patterns_from_module(new_namespace)
        
        # Generate the NFA code string and execute it
        print("Patterns: ")
        print(patterns)
        gen_nfa = generate_nfa(patterns)
        print("gen_nfa() returned string: \n" + gen_nfa)
        exec(gen_nfa)

        # Update the UI with token types
        items = []
        items.append(ft.Container(content=ft.Text("Token Types: ", weight=ft.FontWeight.BOLD), padding=5
                                  ))
        for key in patterns:
            items.append(
                ft.Container(
                    content=ft.Text(key),
                    alignment=ft.alignment.center,
                    padding=5,
                )
            )
        
        token_container.content = ft.Row(controls=items)
        token_container.border = ft.border.all(3, ft.colors.BLACK)

        # Update the terminal output in the UI
        if build_out.getvalue():
            text_output = ("terminal output >>> " + build_out.getvalue())
        else:
            text_output = ""
        terminal_output.content = ft.Text(text_output, selectable=True)
        terminal_output.update()
        
        # sys.stdout = old_out
        
        # Update the automata visualization in the UI
        automata_container.content = ft.Image(src=f"nfa_{timestamp_str}.png", width=600, height=600)
        
        # Save the provided language rules to a Python file
        with open(f'ply_module_{build_counter}.py', 'w') as f:
            f.write(rules_string)
        
        
        column.update()
    
    global lexers
    lexers = []
    
    def compile_button_click(e):
        
        """
        Event handler for the "Compile" button click.
        
        Processes the source code, performs lexical, syntax, and optional semantic analysis,
        and updates the UI with the results.
        
        Parameters:
        - e: Event object (usually provided by event handlers but not used in this function).
        """

        result_message_container.content = ft.Row(controls=results_row)
        result_message_container.border=ft.border.all(3, ft.colors.BLACK)
        result_message_container.padding=5

        global ast_timestamp_string
        global sym_table, sem_errors

        # Clear previous symbol table and semantic error lists
        global sem_visual_removed
        sym_table.clear()
        sem_errors.clear()
        if sem_visual_removed == False:
            errors_container.content = None
            sym_table_container.content = None
            sem_visual_removed = True

        # Reset result messages in the UI containers
        lex_result_message_cont.content = ft.Text("")
        parse_result_message_cont.content = ft.Text("")
        sem_result_message_cont.content = ft.Text("")
        label_result_message_cont.content = ft.Text("None")

        global code_string
        code_string = code.value 
        code_string = code_string.replace("¨", "\"")
        code_string = code_string.replace("´", "\'")

        compile_out = io.StringIO()        
        # sys.stdout= compile_out
        
        # Build the lexer using the PLY library
        build_lexer = f'''import ply_module_{build_counter} \nlexers.append(lex.lex(module = ply_module_{build_counter}))'''
        exec(build_lexer, globals())

        global lex_counter
        lex_counter = lex_counter + 1
        
        global lexer
        lexers[lex_counter-1].input(code_string)
       
        # Display lexical analysis results in the UI
        table = get_lex_table(lexers[lex_counter-1])
        lex_container.content = table
        lex_result_message_cont.content = ft.Text("Lexical")
        label_result_message_cont.content = ft.Text("")

        
        if compile_out.getvalue():
            text_output = ("terminal output >>> " + compile_out.getvalue())
        else:
            text_output = ""

        terminal_output2.content = ft.Text(text_output)
        terminal_output2.update()
        
        # sys.stdout = old_out
        
        # Build the parser and generate the Abstract Syntax Tree (AST)
        ast_timestamp_string = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
        build_parser = f'''parser = yacc.yacc(write_tables=False, module=ply_module_{build_counter}) \nast = parser.parse(code_string, lexers[-1])'''
        exec(build_parser, globals())
        
        global ast
        
        if ((type(ast[0]) is tuple) and (type(ast[0][0]) is tuple)):
            ast = ast[0] + (ast[1],)
        
        # Visualize and display the AST in the UI
        
        print("visualise_ast() ast parameter: ")
        print(ast)
        visualize_ast(ast, f'ast_tree_{ast_timestamp_string}')
        print("visual_ast() output file called " + f'ast_tree_{ast_timestamp_string}')
        print()
        
        
        syntax_container.content = ft.Image(src=f"ast_tree_{ast_timestamp_string}.png", width=600, height=400, fit=ft.ImageFit.CONTAIN)
        parse_result_message_cont.content = ft.Text("Syntax")
        label_result_message_cont.content = ft.Text("")
       
        column2.update()

        if sem_checkbox.value and (not assignment_token_input.value or not symbol_token_input.value):
            column2.controls.append(ft.Text("Please specify the Assignment Token and Variable Symbol Token for semantic analysis."))
            return  

        
        global type_to_value
        assignment_op = type_to_value.get(assignment_token_input.value)


        # Perform semantic analysis if selected in the UI
        if sem_checkbox.value == True:
            
            print("traverse_ast_for_semantics Input: ")
            print("ast: ")
            print(ast)
            print("assign_op: ")
            print(assignment_op)
            print("symbol_token: ")
            print(symbol_token_input.value)
            print("errors before: ")
            print(sem_errors)
            print("symbol table before: ")
            print(sym_table)

            traverse_ast_for_semantics(ast, assignment_op, symbol_token_input.value)

            print("traverse_ast_for semantics Output: ")
            print(ast)
            print("assign_op: ")
            print(assignment_op)
            print("symbol_token: ")
            print(symbol_token_input.value)
            print("errors after: ")
            print(sem_errors)
            print("symbol table after: ")
            print(sym_table)


            if not sem_errors:
                sem_errors.append(["None", "None"])
          
            # print(sem_errors)
            errors_container.content = get_sem_error_table(sem_errors)

            # print(sym_table)
            sym_table_container.content = get_symbol_table(sym_table)

            sem_result_message_cont.content = ft.Text("Semantic")

            sem_visual_removed = False

            column2.update()
    
    def checkbox_changed(e):
        if sem_checkbox.value == True:
            sem_container.content = assign_tooltip
            sem_container2.content = symbol_tooltip
            column2.update()
        else:
            sem_container.content = None
            sem_container2.content = None
            column2.update()
    


    # ======================
    # VIEW
    # ======================

    page.title = "DSLDoodle"
    page.fonts = {"Caveat": "static/Caveat-SemiBold.ttf"}
    page.appbar = ft.AppBar(title=ft.Text("DSLDoodle: Sketch your Domain Specific Language", font_family="Caveat", size=30),
                            bgcolor=ft.colors.BLUE,
                            center_title= True
                            )

    scroll_theme = ft.ScrollbarTheme(thumb_visibility=True, thumb_color=ft.colors.BLUE, 
                                     track_visibility=True, track_color=ft.colors.GREY_200)    
    theme = ft.Theme(scrollbar_theme=scroll_theme)
    page.theme = theme

    
    # COLUMN 1
    
    rules = ft.TextField(label = "Enter language rules here", 
                         multiline = True
                         )
    
    build_language_button = ft.ElevatedButton(text = "Build Language", on_click= build_button_click)

    assignment_token_input = ft.TextField(label = "Name of Token Type for Variable Assignment:", icon=ft.icons.ARROW_FORWARD)
    symbol_token_input = ft.TextField(label = "Name of Token Type for Variable Names:", icon=ft.icons.ARROW_FORWARD)

    assign_tooltip = ft.Tooltip(content=assignment_token_input, message="Enter the token type that is used to assign values to variables.")
    symbol_tooltip = ft.Tooltip(content=symbol_token_input, message="Enter the token type used to represent variable or identifier names.")

    sem_checkbox = ft.Checkbox(label="Do a Semantic Analysis", on_change=checkbox_changed)
    sem_tooltip = ft.Tooltip(content = sem_checkbox, 
                             message="Checks if variables are: \n 1. Defined only once. \n 2. Defined before use.")

    sem_container = ft.Container()
    sem_container2 = ft.Container()

    suffix_container = ft.Container(content=ft.Text("import ply.lex as lex \nimport ply.yacc as yacc"))
    prefix_container = ft.Container(content = ft.Text("lexer = lex.lex() \nparser = yacc.yacc() "))

    token_container = ft.Container()
    
    automata_container = ft.Container(border=ft.border.all(3, ft.colors.BLACK))

    terminal_output = ft.Container(content = ft.Text(""))
    
    column = ft.Column(col={"sm": 6}, controls=[suffix_container, rules, prefix_container, 
                                                build_language_button,
                                                token_container, automata_container,
                                                terminal_output
                                                ],
                       scroll=ft.ScrollMode.ALWAYS,
                       height=500
                       )


    # COLUMN 2

    code = ft.TextField(label = "Enter source code in the language you built here", 
                         multiline = True 
                         )
    
    compile_code_button = ft.ElevatedButton(text = "Compile Code", on_click=compile_button_click)

    label_result_message = ft.Text("None")
    label_result_message_cont = ft.Container(content=label_result_message, padding=5)
    lex_result_message_cont = ft.Container(padding=5)
    parse_result_message_cont = ft.Container(padding=5)
    sem_result_message_cont = ft.Container(padding=5)
    sem_result_tt = ft.Tooltip(content=sem_result_message_cont, message="Scroll down to view Semantic checks and Symbol Table")
    results_row = [ft.Container(ft.Text("DSL Code Analysis Completed: ", weight=ft.FontWeight.BOLD)), label_result_message_cont, lex_result_message_cont, parse_result_message_cont, sem_result_tt]
    result_message_container = ft.Container()
    
    terminal_output2 = ft.Container(content = ft.Text(""))
    
    lex_container = ft.Container()
    syntax_container = ft.Container(border=ft.border.all(3, ft.colors.BLACK))
    errors_container = ft.Container()
    sym_table_container = ft.Container()
    
    column2 = ft.Column(col={"sm": 6}, controls=[code, sem_tooltip, sem_container, sem_container2, 
                                                compile_code_button, 
                                                result_message_container, terminal_output2, 
                                                lex_container, syntax_container, errors_container, sym_table_container,
                                                ],
                        scroll=ft.ScrollMode.ALWAYS,
                        height=500
                        )

    
    # Row
    row = ft.ResponsiveRow([column, column2])
    page.add(row)


ft.app(target=main, port=8550)