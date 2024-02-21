use std::{ops::Deref, path::Path};

use crate::{
    ast, graph::CrateId, hir::def_map::Visibility, monomorphization::ast::Function, parser::SortedModule, AssignStatement, BlockExpression, CallExpression, CastExpression, ConstructorExpression, Expression as NoirExpression, ExpressionKind, ForLoopStatement, ForRange, FunctionDefinition as NoirFunctionDefinition, FunctionReturnType, Ident as NoirIdent, IfExpression, IndexExpression, InfixExpression, LValue, LetStatement, Literal, MemberAccessExpression, MethodCallExpression, NoirFunction, NoirStruct, Path as NoirPath, Pattern, PrefixExpression, Signedness, Statement as NoirStatement, StatementKind, UnaryOp, UnresolvedType, UnresolvedTypeData
};
use acvm::FieldElement;
use fm::{FileId, FileManager};
use noirc_errors::{Span, Spanned};
use solang_parser::{
    parse,
    pt::{
        ContractPart, Expression as SolExpression, FunctionDefinition as SolFunction, Identifier as SolIdent, Parameter as SolParameter, ParameterList, SourceUnitPart, Statement as SolStatement, StructDefinition, Type
    },
};

use crate::{parser::ParserError, BinaryOpKind};

pub fn parse_sol_file(fm: &FileManager, file_id: FileId) -> (SortedModule, Vec<ParserError>) {
    let file = fm.fetch_file(file_id);

    // TODO: bring in errors
    let errors = vec![];
    (parse_sol(file.source()), errors)
}

pub fn parse_sol(text: &str) -> SortedModule {
    let (tree, _) = parse(&text, 0).unwrap();

    let mut ast = SortedModule::default();

    // Janky add builtins
    // let mut builtins = generate_builtins();
    // ast.functions.append(&mut builtins);

    // Janky add globals
    let (globals, mut structs) = generate_globals();
    ast.types.append(&mut structs);

    for part in &tree.0 {
        match part {
            SourceUnitPart::ContractDefinition(def) => {
                for part in &def.parts {
                    match part {
                        ContractPart::FunctionDefinition(def) => {
                            let transformed = transform_function(&def, &ast, &globals);
                            ast.functions.push(transformed);
                        },
                        ContractPart::StructDefinition(def) => {
                            let transformed = transform_struct(&def);
                            ast.types.push(transformed);
                        }
                        _ => (),
                    }
                }
            }
            _ => (),
        }
    }

    ast
}

fn giga_jank_parse(defaults: &str) -> Vec<NoirStruct> {
    let (tree, _) = parse(&defaults, 0).unwrap();

    let mut results = vec![];
    for part in &tree.0 {
        match part {
            SourceUnitPart::ContractDefinition(def) => {
                for part in &def.parts {
                    match part {
                        ContractPart::StructDefinition(def) => {
                            results.push(transform_struct(&def));
                        },
                        _ => ()
                    }
                }
            },
            _ => (),
        }
    }

    results
}

fn generate_globals() -> (Vec<LetStatement>, Vec<NoirStruct>) {
    // TODO: Actually fill these out. Probably a better approach exists. 
    // This was conceived in ... <10 seconds. 
    let defaults = r#"
        contract defaults {
            struct msg {
                uint256 sender;
            }
        }
    "#;

    let structs = giga_jank_parse(defaults);

    let globals = vec!["msg"];

    let mut results = vec![];
    for (g, st) in globals.iter().zip(structs.clone()) {
        let mut fields = vec![];
        for f in st.fields.iter() {
            fields.push((make_ident(f.0.to_string().as_str()), make_numeric_literal("0".to_string())))
        }
        let ty_name = path(make_ident(&st.name.to_string()));

        let exp =  NoirExpression::new(
            ExpressionKind::Constructor(Box::new(ConstructorExpression { type_name: ty_name.clone(), fields })),
            Span::default()
        );

        let s = LetStatement {
            pattern: pattern(g),
            r#type: make_type(UnresolvedTypeData::Named(ty_name, vec![])),
            expression: exp,
        };
        results.push(s)
    }
    
    (results, structs)
}

fn generate_builtins() -> Vec<NoirFunction> {
    let functions = vec!["keccak256"];

    let mut results = vec![];
    for i in functions.iter() {
        // TODO: remove unwrap
        let name_ident = NoirIdent::new(i.to_string(), Span::default());
        let params = Vec::new();

        // TODO: Add per function, use the correct types
        // How can we make this actually correct?
        let return_type = make_type(UnresolvedTypeData::FieldElement);
        let return_type = FunctionReturnType::Ty(return_type);

        let mut noir_function = NoirFunctionDefinition::normal(
            &name_ident,
            &params,
            &Vec::new(),
            &BlockExpression(Vec::new()),
            &Vec::new(),
            &return_type,
        );
        noir_function.return_visibility = ast::Visibility::Public;
        results.push(NoirFunction::normal(noir_function));
    }

    return results
}

fn transform_struct(sol_struct: &StructDefinition) -> NoirStruct {
    let name_ident = transform_ident(&sol_struct.name.as_ref().unwrap());

    let mut fields = vec![];
    for f in sol_struct.fields.iter() {
        let name = transform_ident(&f.name.as_ref().unwrap());
        let ty = match f.ty.clone() {
            // Built in types
            SolExpression::Type(_, typ) => {
                // TODO: handle types, for now pretend they're all field elements.
                make_type(UnresolvedTypeData::FieldElement)
            },
            // Custom types
            SolExpression::Variable(ident) => {
                let p = path(make_ident(&ident.to_string()));
                // TODO: does this have to have the list of fields on the type?
                // For the nested "Location" object. 
                make_type(UnresolvedTypeData::Named(p, vec![]))
            }
            _ => panic!("no match type={:?}", f.ty),
        };
        
        fields.push((name, ty));
    }
    // Location & Tile, two structures. 
    println!("=== DEBUG(noir): struct={:?}, fields={:?}", name_ident, fields);

    NoirStruct {
        name: name_ident, 
        generics: Vec::new(),
        attributes: Vec::new(),
        span: Span::default(),
        fields: fields
    }
}

fn transform_function(sol_function: &SolFunction, ast: &SortedModule, globals: &Vec<LetStatement>) -> NoirFunction {
    let params = transform_parameters(&sol_function.params);

    // TODO: yeet clone
    let body = transform_body(sol_function.body.clone(), ast, globals);
    let return_type = transform_return_type(&sol_function.returns.as_ref());

    // Ignore generics and trait bounds
    let generics = Vec::new();
    let trait_bounds = Vec::new();

    // TODO: remove unwrap
    let name_ident = transform_ident(&sol_function.name.as_ref().unwrap());

    let mut noir_function = NoirFunctionDefinition::normal(
        &name_ident,
        &generics,
        &params,
        &body,
        &trait_bounds,
        &return_type,
    );

    // If we have a return type then we need to make it public; this is not handled by the normal function definition above
    // TODO: probably more sense to match this on the name being main
    if !matches!(return_type, FunctionReturnType::Default(_)) {
        noir_function.return_visibility = ast::Visibility::Public;
    }

    NoirFunction::normal(noir_function)
}

fn transform_ident(identifier: &SolIdent) -> NoirIdent {
    NoirIdent::new(identifier.name.clone(), Span::default())
}

fn transform_parameters(sol_params: &ParameterList) -> Vec<(NoirIdent, UnresolvedType)> {
    // Filter out the spans
    let params: Vec<&SolParameter> =
        sol_params.iter().map(|param| &param.1).filter_map(|v| v.as_ref()).collect();

    let mut out_params = Vec::new();

    for param in params {
        let name = transform_ident(&param.name.as_ref().expect("Must have a name?"));
        let ty = match param.ty.clone() {
            SolExpression::Type(_, typ) => {
                match typ {
                    Type::Int(256) => make_type(UnresolvedTypeData::Integer(Signedness::Unsigned, 256)),
                    // TODO: more types.
                    _ => make_type(UnresolvedTypeData::FieldElement),
                }
            },
            SolExpression::Variable(ident) => {
                let p = path(make_ident(&ident.to_string()));
                make_type(UnresolvedTypeData::Named(p, vec![]))
            },
            _ => panic!("unsupport type in function paramters ty={:?}", param.ty)
        };

        out_params.push((name, ty));
    }

    out_params
}

fn transform_body(sol_body: Option<SolStatement>, ast: &SortedModule, globals: &Vec<LetStatement>) -> BlockExpression {
    let sol_body = sol_body.expect("Must have a body");

    let mut statements = Vec::new();
    for s in globals.iter() {
        statements.push(NoirStatement {
            kind: StatementKind::Let(s.clone()),
            span: Span::default(),
        });
    };

    statements.append(&mut resolve_statement(sol_body, ast));
    BlockExpression(statements)
}

fn resolve_statement(sol_body: SolStatement, ast: &SortedModule) -> Vec<NoirStatement> {
    let mut collected_statements: Vec<NoirStatement> = Vec::new();

    match sol_body {
        SolStatement::Block { loc, unchecked, statements } => {
            for statement in statements {
                collected_statements.append(&mut resolve_statement(statement, ast));
            }
        }
        SolStatement::Expression(_, sol_expression) => {
            let expression = resolve_expression(sol_expression);
            let express_statement = semi_expression(expression);
            collected_statements.push(express_statement);
        }
        SolStatement::Return(_, sol_expression) => {
            if let Some(return_exp) = sol_expression {
                let expression = resolve_expression(return_exp);
                let express_statement = statement_expression(expression);
                collected_statements.push(express_statement);
            }
        }
        SolStatement::VariableDefinition(_, var_def, expression_opt) => {
            // === EXAMPLE === 
            // line: Tile memory updatedFrom = from; 
            // var_def: type = tile, storage = memory, name = updatedFrom
            // expr: from
            
            let name = &var_def.name.unwrap().name;
            let (ty, ty_name) = match var_def.ty.clone() {
                SolExpression::Variable(ident) => {
                    let p = path(make_ident(&ident.to_string()));
                    (UnresolvedTypeData::Named(p.clone(), vec![]), p)
                },
                // TODO: more types. Share logic in other places. 
                SolExpression::Type(_, t) => {
                    let inner_t = match t {
                        Type::Int(256) => UnresolvedTypeData::Integer(Signedness::Unsigned, 256),
                        _ => UnresolvedTypeData::FieldElement,
                    };

                    (inner_t, path(make_ident("")))
                },
                _ => panic!("unsupported type tp={:?}", var_def.ty)
            };

            // Two Steps:
            // First, define the variable in the scope
            // Second, handle assignment to that variable (either default or actual)

            let assign = if let Some(expression) = expression_opt {
                let exp = resolve_expression(expression);
                let sa = mutable_assignment(name, ty, exp.clone());
                var_assignment(variable(name), exp);
                sa
            } else {
                let val = make_numeric_literal("0".to_string());
                let sa = mutable_assignment(name, ty, val.clone());
                var_assignment(variable(name), val);
                sa
            };

            println!("=== DEBUG(noir): Adding statement for variable decl stmt={:?}", assign);
            collected_statements.push(assign);
        }
        SolStatement::If(_, expr, inner, outer) => {
            // TODO Note if in an if statement
            // Early return is NOT supported

            let expr = resolve_expression(expr);
            let inner2 = block_expression(resolve_statement(*inner, ast));
            let outer2 = outer.clone();
            let outer3 = outer2
                .clone()
                .and(Some(block_expression(resolve_statement(*(outer2.unwrap().clone()), ast))));

            collected_statements.push(make_if(expr, inner2, outer3));
        }
        SolStatement::For(_, initialise, end_condition, between_condition, body) => {
            // We want to get the name out of this - TODO: the type
            let (init_name, starting_value) = get_name_and_value_from_sol_for_loop_init(initialise);
            let init_ident = make_ident(init_name.as_str());
            let end_number = get_end_via_expression(end_condition);

            let start_number = make_numeric_literal(starting_value);
            // let end_number = make_numeric_literal(end_number);

            let inner_body = resolve_statement(*body.expect("For loop must have a body"), ast);
            // dbg!(_between_condition); TODO: work with the between condition

            let for_loop =
                make_for(init_ident, start_number, end_number, block_expression(inner_body));
            collected_statements.push(for_loop);
        }
        _ => panic!("Not implemented statement, {sol_body}"),
    }
    collected_statements
}

fn get_name_and_value_from_sol_for_loop_init(
    initialize: Option<Box<SolStatement>>,
) -> (String, String) {
    let init = initialize.expect("In solnoir you must initialise a variable in your for loop");
    match init.as_ref() {
        SolStatement::VariableDefinition(_, var_def, expression) => {
            let name = var_def.clone().name.unwrap().name;

            let exp = expression.clone().expect("For loop assignments MUST have a value");
            let value = match exp {
                SolExpression::NumberLiteral(_, val, _exp, _unit) => val.clone(),
                _ => panic!("For loop assignments MUST have a value"),
            };

            (name, value)
        }
        _ => panic!("Statement other than variable definition found in for loop initialise"),
    }
}


fn get_end_via_expression(end_condition: Option<Box<SolExpression>>) -> NoirExpression {
    let end = end_condition.expect("In solnoir you must initialise a variable in your for loop");

    match end.as_ref() {
        SolExpression::Less(_, _, num) => {
            println!("Matched num: {:?}", num);
            let e = num.as_ref().clone();
            let noir_expr = resolve_expression(e);
            return noir_expr;
            // variable( ident (proof), ident(length)) 
            // How to translate this? 

            // return match num.as_ref() {
            //     SolExpression::NumberLiteral(_, val, _, _) => val.clone(),
            //     _ => panic!("For loop assignments MUST have a value"),
            // };
        }
        _ => panic!("Loop conditionals only implemented for < operator"),
    }
}

fn get_end_condition_from_sol_for_loop_end(end_condition: Option<Box<SolExpression>>) -> String {
    let end = end_condition.expect("In solnoir you must initialise a variable in your for loop");

    println!("Loop end {:?}", end);

    match end.as_ref() {
        SolExpression::Less(_, _, num) => match num.as_ref() {

            SolExpression::NumberLiteral(_, val, _, _) => val.clone(),
            _ => panic!("For loop assignments MUST have a value"),
        },
        _ => panic!("Loop conditionals only implemented for < operator"),
    }
}

fn arith_expression(
    lhs: SolExpression,
    rhs: SolExpression,
    operator: BinaryOpKind,
) -> NoirExpression {
    let lhs = resolve_expression(lhs);
    let rhs = resolve_expression(rhs);
    infix_expression(lhs, rhs, operator)
}

fn assign_and_arith_expression(
    lhs: SolExpression,
    rhs: SolExpression,
    operator: BinaryOpKind,
) -> NoirExpression {
    let assign_to = resolve_expression(lhs.clone());
    let assign_value = arith_expression(lhs, rhs, operator);
    let assignment_name = var_assignment(assign_to, assign_value);

    block_expression(vec![assignment_name])
}

fn resolve_expression(sol_expression: SolExpression) -> NoirExpression {
    match sol_expression {
        // Arithmetic
        SolExpression::Add(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Add),
        SolExpression::Subtract(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::Subtract)
        }
        SolExpression::Equal(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Equal),
        SolExpression::Divide(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Divide),
        SolExpression::NotEqual(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::NotEqual)
        }
        SolExpression::Less(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Less),
        SolExpression::LessEqual(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::LessEqual)
        }
        SolExpression::More(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Greater),
        SolExpression::MoreEqual(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::GreaterEqual)
        }
        SolExpression::And(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::And),
        SolExpression::Or(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Or),
        SolExpression::BitwiseXor(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Xor),
        SolExpression::ShiftLeft(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::ShiftLeft)
        }
        SolExpression::ShiftRight(_, lhs, rhs) => {
            arith_expression(*lhs, *rhs, BinaryOpKind::ShiftRight)
        }
        SolExpression::Modulo(_, lhs, rhs) => arith_expression(*lhs, *rhs, BinaryOpKind::Modulo),
        SolExpression::PostIncrement(_, expr) => {
            let expr = resolve_expression(*expr);
            let one = make_numeric_literal("1".to_string());
            infix_expression(expr, one, BinaryOpKind::Add)
        }
        SolExpression::PostDecrement(_, expr) => {
            let expr = resolve_expression(*expr);
            let one = make_numeric_literal("1".to_string());
            infix_expression(expr, one, BinaryOpKind::Subtract)
        }
        SolExpression::AssignAdd(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Add)
        }
        SolExpression::AssignSubtract(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Subtract)
        }
        SolExpression::AssignDivide(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Divide)
        }
        SolExpression::AssignModulo(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Modulo)
        }
        SolExpression::AssignMultiply(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Multiply)
        }
        SolExpression::AssignShiftLeft(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::ShiftLeft)
        }
        SolExpression::AssignShiftRight(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::ShiftRight)
        }
        SolExpression::AssignOr(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Or)
        }
        SolExpression::AssignAnd(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::And)
        }
        SolExpression::AssignXor(_, lhs, rhs) => {
            assign_and_arith_expression(*lhs, *rhs, BinaryOpKind::Xor)
        }
        SolExpression::Variable(ident) => {
            // Creates a variable with kind=plain
            let ident = transform_ident(&ident);
            variable_ident(ident)
        }

        // How to handle array type?
        SolExpression::MemberAccess(_, expr, ident) => {
            member_access(expr.to_string().as_str(), ident.to_string().as_str())
        }

        SolExpression::ArraySubscript(_, ident, Some(rhs)) => {
            let index = resolve_expression(*rhs);
            index_array(make_ident(ident.to_string().as_str()), index.to_string().as_str())
        }

        SolExpression::FunctionCall(_, lhs, rhs) => {
            let expr = resolve_expression(*lhs);
            let mut args = vec![];
            for e in rhs {
                let result = resolve_expression(e);
                args.push(result);
            }

            call(expr, args)
        }

        SolExpression::New(_, lhs) => {
            // TODO: Extra janky handling of new objects.
            match lhs.as_ref() {
                SolExpression::FunctionCall(_, lhs, rhs) => {
                    let type_name = ast::Path::from_ident(make_ident(lhs.to_string().as_str()));

                    let mut fields = vec![];
                    for (i, e) in rhs.iter().enumerate() {
                        fields.push((make_ident(i.to_string().as_str()), resolve_expression(e.clone())))
                    }

                    return NoirExpression::new(
                        ExpressionKind::Constructor(Box::new(ConstructorExpression { type_name, fields })),
                        Span::default()
                    )
                },
                _ => panic!("Not implemented expression, {lhs}"),
            }
        }

        SolExpression::HexNumberLiteral(_, lhs, _) => {
            expression(ExpressionKind::Literal(Literal::Str(lhs)))
        }

        SolExpression::HexLiteral(lhs) => {
            let mut s = String::new();
            for b in lhs.iter() {
                s = s + b.hex.as_str();
            }
            expression(ExpressionKind::Literal(Literal::Str(s)))
        }

        // TODO: support exp / unit
        // Value is the most common
        // exp is if the number is exponented?
        // unit is days / ether that can follow
        SolExpression::NumberLiteral(_, val, _exp, _unit) => make_numeric_literal(val),
        SolExpression::Assign(_, lhs, rhs) => {
            let lhs = resolve_expression(*lhs);
            let rhs = resolve_expression(*rhs);

            println!("=== DEBUG(noir): Attempting var_assignment, lhs={:?}, rhs={:?}", lhs, rhs);
            // yuck
            block_expression(vec![var_assignment(lhs, rhs)])
        }

        SolExpression::AddressLiteral(_, val) => {
            println!("Inside address {:?}", val);
            expression(ExpressionKind::Literal(Literal::Str(val)))
        }

        SolExpression::StringLiteral(val) => {
            println!("Inside string literal {:?}", val);
            expression(ExpressionKind::Literal(Literal::Str(val.last().unwrap().to_string())))
        }

        // TODO: How do we handle types here? 
        SolExpression::Type(_, val) => {
            match val {
                // Type::Address => expression(ExpressionKind::Literal(Literal::Unit)),
                // Type::Uint(256) => expression(ExpressionKind::Literal(Literal::Unit)),
                _ => panic!("Not implemented type {:?}", val),
            }   
        }

        _ => panic!("Not implemented expression, {:?}", sol_expression),
    }
}

// fn transform_statement() -> NoirStatement {}

fn transform_return_type(sol_params: &ParameterList) -> FunctionReturnType {
    // Filter out the spans
    let params: Vec<&SolParameter> =
        sol_params.iter().map(|param| &param.1).filter_map(|v| v.as_ref()).collect();

    if params.len() > 0 {
        let ty = make_type(UnresolvedTypeData::FieldElement);
        FunctionReturnType::Ty(ty)
    } else {
        FunctionReturnType::Default(Span::default())
    }
}

//
//
//
//
//
//
//
//
//             Helpers for creating noir ast nodes
//
fn make_ident(name: &str) -> NoirIdent {
    NoirIdent::new(name.to_string(), Span::default())
}

fn ident_path(name: &str) -> NoirPath {
    NoirPath::from_ident(make_ident(name))
}

fn path(ident: NoirIdent) -> NoirPath {
    NoirPath::from_ident(ident)
}

fn expression(kind: ExpressionKind) -> NoirExpression {
    NoirExpression::new(kind, Span::default())
}

fn block_expression(statements: Vec<NoirStatement>) -> NoirExpression {
    expression(ExpressionKind::Block(BlockExpression(statements)))
}

fn infix_expression(
    lhs: NoirExpression,
    rhs: NoirExpression,
    operator: BinaryOpKind,
) -> NoirExpression {
    expression(ExpressionKind::Infix(Box::new(InfixExpression {
        lhs,
        rhs,
        operator: Spanned::from(Span::default(), operator),
    })))
}

fn variable(name: &str) -> NoirExpression {
    let p = ident_path(name);
    expression(ExpressionKind::Variable(p))
}

fn variable_ident(identifier: NoirIdent) -> NoirExpression {
    let p = path(identifier);
    expression(ExpressionKind::Variable(p))
}

fn variable_path(path: NoirPath) -> NoirExpression {
    expression(ExpressionKind::Variable(path))
}

fn method_call(
    object: NoirExpression,
    method_name: &str,
    arguments: Vec<NoirExpression>,
) -> NoirExpression {
    expression(ExpressionKind::MethodCall(Box::new(MethodCallExpression {
        object,
        method_name: make_ident(method_name),
        arguments,
    })))
}

fn call(func: NoirExpression, arguments: Vec<NoirExpression>) -> NoirExpression {
    expression(ExpressionKind::Call(Box::new(CallExpression { func: Box::new(func), arguments })))
}

fn pattern(name: &str) -> Pattern {
    Pattern::Identifier(make_ident(name))
}

fn mutable(name: &str) -> Pattern {
    Pattern::Mutable(Box::new(pattern(name)), Span::default())
}

// fn struct_decl(name: &str) -> Pattern {
//     let p = path(make_ident(name));
//     Pattern::Struct(p, Vec::new(), Span::default())
// }

// TODO: This code is bad. It's creating structures for a Noir style constructor pattern. 
// This may be needed for struct construction. 
fn struct_assignment(path: NoirPath, ty: UnresolvedTypeData, assigned_to: NoirExpression, ast: &SortedModule) -> NoirStatement {
    println!("===DEBUG(noir): DECLARING STRUCT, name={}", path);
    
    let ty_name = match ty.clone() {
        UnresolvedTypeData::Named(p, _) => {
            p
        },
        _ => panic!("Cannot create assignment for struct with unnamed type.")
    };

    // Extreme hack: Fixes struct assignments. Lookup the matching
    // type in the AST, then passthrough the fields we expect. 
    let mut fields = vec![];
    for t in ast.types.clone().iter() {
        if t.name.to_string() == ty_name.as_ident().unwrap().to_string() {
            for f in t.fields.iter() {
                fields.push((f.0.clone(), pattern(&f.1.to_string())));
            }
        }
    }
    
    make_statement(StatementKind::Let(LetStatement {
        pattern: Pattern::Struct(ty_name, fields, Span::default()),
        r#type: make_type(ty),
        expression: assigned_to,
    }))
}

fn mutable_assignment(name: &str, ty: UnresolvedTypeData, assigned_to: NoirExpression) -> NoirStatement {
    make_statement(StatementKind::Let(LetStatement {
        pattern: mutable(name),
        r#type: make_type(ty),
        expression: assigned_to,
    }))
}

fn mutable_reference(variable_name: &str) -> NoirExpression {
    expression(ExpressionKind::Prefix(Box::new(PrefixExpression {
        operator: UnaryOp::MutableReference,
        rhs: variable(variable_name),
    })))
}

fn let_assignment(name: &str, assigned_to: NoirExpression) -> NoirStatement {
    make_statement(StatementKind::Let(LetStatement {
        pattern: pattern(name),
        r#type: make_type(UnresolvedTypeData::Unspecified),
        expression: assigned_to,
    }))
}

fn var_assignment(var: NoirExpression, assigned_to: NoirExpression) -> NoirStatement {
    // TODO: yuck.
    match var.kind {
        ExpressionKind::Variable(path) => {
            let name = path.segments.last().unwrap().0.contents.clone();
            println!("===DEBUG(noir): VAR_ASSIGNMENT name={:?}, assigned={:?}", name, assigned_to);

            make_statement(StatementKind::Assign(AssignStatement {
                lvalue: LValue::Ident(make_ident(&name)),
                expression: assigned_to,
            }))
        },
        ExpressionKind::MemberAccess(expr) => {
            // NOTE: Resolved the plain::updatedFrom bug, by removing the plain component of the path. 
            let name = match expr.lhs.kind.clone() {
                ExpressionKind::Variable(p) => {
                    p.segments.last().unwrap().0.contents.clone()
                },
                _ => panic!("Only support variable assignments expr={:?}", expr)
            };
            
            make_statement(StatementKind::Assign(AssignStatement {
                lvalue: LValue::MemberAccess { object: Box::new(LValue::Ident(make_ident(&name))), field_name: expr.rhs },
                expression: assigned_to,
            }))
        },
        _ => panic!("Not a variable kind={:?}, var={:?}", var.kind, var),
    }
}

fn assignment(name: &str, assigned_to: NoirExpression) -> NoirStatement {
    make_statement(StatementKind::Assign(AssignStatement {
        lvalue: LValue::Ident(make_ident(name)),
        expression: assigned_to,
    }))
}

fn statement_expression(expression: NoirExpression) -> NoirStatement {
    make_statement(StatementKind::Expression(expression))
}

// This is the most likely in this context
fn semi_expression(expression: NoirExpression) -> NoirStatement {
    make_statement(StatementKind::Semi(expression))
}

fn member_access(lhs: &str, rhs: &str) -> NoirExpression {
    let v = variable(lhs);
    let r = make_ident(rhs);

    println!("=== DEBUG(noir): MEMBER_ACCESS lhs={:?},  rhs={:?}", v, r);
    expression(ExpressionKind::MemberAccess(Box::new(MemberAccessExpression {
        lhs: v,
        rhs: r,
    })))
}

fn make_statement(kind: StatementKind) -> NoirStatement {
    NoirStatement { span: Span::default(), kind }
}

fn make_if(
    condition: NoirExpression,
    consequence: NoirExpression,
    alternative: Option<NoirExpression>,
) -> NoirStatement {
    make_statement(StatementKind::Expression(expression(ExpressionKind::If(Box::new(
        IfExpression { condition, consequence, alternative },
    )))))
}

fn make_for(
    identifier: NoirIdent,
    start_variable: NoirExpression,
    end_variable: NoirExpression,
    block: NoirExpression,
) -> NoirStatement {
    let range = ForRange::Range(start_variable, end_variable);
    make_statement(StatementKind::For(ForLoopStatement {
        identifier,
        range,
        block,
        span: Span::default(),
    }))
}

fn make_numeric_literal(number: String) -> NoirExpression {
    // expression(ExpressionKind::Literal(Literal::Integer(FieldElement::from_hex(&number).unwrap())))
    // convert from string to number
    let number = number.parse::<u128>().unwrap();
    expression(ExpressionKind::Literal(Literal::Integer(FieldElement::from(number))))
}

macro_rules! chained_path {
    ( $base:expr $(, $tail:expr)* ) => {
        {
            let mut base_path = ident_path($base);
            $(
                base_path.segments.push(ident($tail));
            )*
            base_path
        }
    }
}

macro_rules! chained_dep {
    ( $base:expr $(, $tail:expr)* ) => {
        {
            let mut base_path = ident_path($base);
            base_path.kind = PathKind::Dep;
            $(
                base_path.segments.push(ident($tail));
            )*
            base_path
        }
    }
}

fn cast(lhs: NoirExpression, ty: UnresolvedTypeData) -> NoirExpression {
    expression(ExpressionKind::Cast(Box::new(CastExpression { lhs, r#type: make_type(ty) })))
}

fn make_type(typ: UnresolvedTypeData) -> UnresolvedType {
    UnresolvedType { typ, span: Some(Span::default()) }
}

fn index_array(array: NoirIdent, index: &str) -> NoirExpression {
    expression(ExpressionKind::Index(Box::new(IndexExpression {
        collection: variable_path(path(array)),
        index: variable(index),
    })))
}

fn index_array_variable(array: NoirExpression, index: &str) -> NoirExpression {
    expression(ExpressionKind::Index(Box::new(IndexExpression {
        collection: array,
        index: variable(index),
    })))
}
