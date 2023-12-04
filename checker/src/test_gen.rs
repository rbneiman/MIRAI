use std::{fmt::{Debug, Formatter}, rc::Rc, collections::{HashMap, BTreeMap}};
use log_derive::logfn_inputs;
use rustc_middle::ty::{Ty, TyCtxt};
use std::io::Write;
use crate::{smt_solver::SmtParam, abstract_value::AbstractValue, type_visitor::TypeVisitor, path::PathEnum};
use crate::path::Path;


#[derive(Debug)]
struct ResolvedParam<'tcx>{
    pub ty: Ty<'tcx>,
    pub name: Rc<String>,
    pub type_name: String,
    pub value_string: String,
    pub param_ordinal: Option<usize>,
    pub related_to: usize,
}


#[derive(Debug)]
struct FuncArg<'tcx>{
    pub ty: Ty<'tcx>,
    pub name: Rc<String>,
    pub ordinal: usize,
    pub related_to: BTreeMap<Rc<String>, Rc<ResolvedParam<'tcx>>>,
}

#[derive(Debug)]
struct Testcase<'tcx>{
    pub abstract_val: Rc<AbstractValue>,
    pub param_list: Vec<Rc<ResolvedParam<'tcx>>>,
}

#[derive(Debug)]
struct FuncTestCaseInfo<'tcx>{
    pub func_name: Rc<String>,
    pub param_map: BTreeMap<Rc<String>, Rc<ResolvedParam<'tcx>>>,
    pub testcases: Vec<Testcase<'tcx>>,
    pub args: Vec<FuncArg<'tcx>>,
    pub func_name_raw: Rc<String>,
    // pub arg_types: Vec<Ty<'tcx>>,
    // pub actual_args: Vec<Option<Rc<ResolvedParam<'tcx>>>>,
}

pub struct TestGen<'tcx>{
    test_output_dir: String,
    tcx: TyCtxt<'tcx>,
    testcase_map: BTreeMap<Rc<String>, FuncTestCaseInfo<'tcx>>,
}

impl<'tcx> Debug for TestGen<'tcx> {
    
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        format!("TestGen: {:?}", self.test_output_dir).fmt(f)
    }
}

impl<'tcx> TestGen<'tcx> {
    
    pub fn new(test_output_file: String, tcx: TyCtxt<'tcx>) -> Self{

        TestGen { 
            test_output_dir: test_output_file,
            tcx,
            testcase_map: BTreeMap::new()
        }
    }

    fn grab_top(path: &Rc<Path>) -> Rc<Path>{
        let mut last = path;
        let mut unqualified =  match &path.value{
            PathEnum::QualifiedPath { qualifier, ..  } => Some(qualifier),
            _ => None
        };
        while let Some(qualified) = unqualified {
            last = qualified;
            unqualified =  match &qualified.value{
                PathEnum::QualifiedPath {  qualifier, .. } => Some(qualifier),
                _ => None
            };
        }
        last.clone()
    }


    #[logfn_inputs(TRACE)]
    pub fn add_test(&mut self, 
            function_name: &String, 
            val: &Rc<AbstractValue>, 
            params: &Vec<Box<dyn SmtParam>>, 
            ind:usize, 
            type_visitor: &TypeVisitor<'tcx>, 
            current_span: rustc_span::Span,
            debug_names: &HashMap<usize, Rc<String>>){
        
        let function_name_filtered = Rc::new(function_name.replace(".", "_").replace("::", "_"));
        if !self.testcase_map.contains_key(&function_name_filtered){
            let arg_count = type_visitor.mir.arg_count;
            let mut args: Vec<FuncArg> = Vec::new();

            let mut local_iter = type_visitor.mir.local_decls.iter_enumerated();
            local_iter.next();
            for i in 0..arg_count {
                let (local, local_decl) = local_iter.next().unwrap();
                let ty = local_decl.ty.clone();
                let ordinal = local.as_usize();
                let name = debug_names.get(&ordinal).map(|v| v.clone())
                    .unwrap_or(Rc::new(format!("param_{}", ordinal + 1)));
                let related_to = BTreeMap::new();
                
                let func_arg = FuncArg{
                    ty,
                    name,
                    ordinal,
                    related_to
                };
                args.push(func_arg);
            }

            // let func_name_raw = function_name.to_string(),


            self.testcase_map.insert(function_name_filtered.clone(), FuncTestCaseInfo { 
                func_name: function_name_filtered.clone(), 
                param_map: BTreeMap::new(), 
                testcases: Vec::new(), 
                args,
                func_name_raw: Rc::new(function_name.clone()),
            });
        }
        let func_info = self.testcase_map.get_mut(&function_name_filtered).unwrap();

        let mut resolved_params: Vec<Rc<ResolvedParam>> = Vec::new();
        for param in params{
            let name = Rc::new(param.get_debug_name(debug_names));
            let path = param.get_path().unwrap();
            let ty = type_visitor.get_path_rustc_type(&path, current_span);
            let type_name = ty.to_string();
            let value_string = param.get_val().to_string();
            let param_ordinal = match path.value {
                PathEnum::Parameter { ordinal } => Some(ordinal),
                _ => None
            };

            let unqualified = Self::grab_top(&path);
            let related_to = unqualified.get_ordinal();
            println!("test_gen name: {:?}, path: {:?}, unqualified: {:?}", name, path, unqualified);

            let resolved = Rc::new(ResolvedParam{
                name,
                ty,
                type_name,
                value_string,
                param_ordinal,
                related_to
            });

            let arg = &mut func_info.args[related_to - 1];
            if !arg.related_to.contains_key(&resolved.name) {
                arg.related_to.insert(resolved.name.clone(), resolved.clone());
            }
            
            if !func_info.param_map.contains_key(&resolved.name){
                func_info.param_map.insert(resolved.name.clone(), resolved.clone());
            }

            resolved_params.push(resolved);
        }

        func_info.testcases.push(Testcase { 
            abstract_val: val.clone(), param_list: resolved_params 
        })

    }

    fn output_testcase(&self, test_ind: usize, func_info: &FuncTestCaseInfo<'tcx>, testcase: &Testcase<'tcx>) -> String{
        let intializers_string: String = testcase.param_list.iter()
            .map(|param| format!("        let {}: {} = {};\n", param.name, param.type_name, param.value_string))
            .collect();

        let mut resolved_args: Vec<Option<&Rc<ResolvedParam>>> = Vec::new();
        resolved_args.resize(func_info.args.len(), None);
        for resolved in testcase.param_list.iter(){
            if let Some(ord) = resolved.param_ordinal{
                resolved_args[ord - 1] = Some(resolved);
            }
        }

        trace!("Test ind: {}", test_ind);
        trace!("Args: {:?}", func_info.args);
        trace!("Resolved: {:?}", resolved_args);

        let mut constructor_param_initializers = String::new();
        let mut func_call_param_string = String::new();
        for i in 0..func_info.args.len(){

            if let Some(resolved) = resolved_args[i] {

                func_call_param_string.push_str(format!("{}, ", resolved.value_string).as_str())
            }else{
                let arg = &func_info.args[i];
                let name = &arg.name;
                
                let mut constructor_params : String = arg.related_to.iter()
                    .map(|(name, related)| 
                        if testcase.param_list.iter().any(|p| name == &p.name){
                            format!("Some({}), ", name)
                        }else{
                            "None, ".to_string()
                        }
                    )
                    .collect();
                
                if constructor_params.len() > 1 {
                    constructor_params.truncate(constructor_params.len() - 2);
                }
                
                constructor_param_initializers.push_str(&format!("        let {}: {} = construct_{}({});\n", 
                        name, arg.ty.to_string(), name, constructor_params
                    )
                );

                func_call_param_string.push_str(format!("{}, ", name).as_str())
            }
            
        }
        
        if func_call_param_string.len() > 1 {
            func_call_param_string.truncate(func_call_param_string.len() - 2);
        }
        

        let func_call_string = format!("{}({});", func_info.func_name_raw, func_call_param_string);
        let out = format!("    #[test]\n    fn test_{}() {{\n{}\n{}\n        {}\n    }}\n\n", test_ind, intializers_string, constructor_param_initializers, func_call_string);
        out
    }

    fn make_constuctor_function(&self, arg: &FuncArg<'tcx>) -> String{
        let mut params: String = arg.related_to.values()
            .map(|param| format!("{}: Option<{}>, ", param.name, param.type_name))
            .collect();
        if params.len() > 1 {
            params.truncate(params.len() - 2);
        }
        format!("    fn construct_{}({}) -> {}{{\n        todo!(\"Make an instance of this struct using the given params.\")\n    }}\n\n", arg.name, params, arg.ty.to_string())
    }

    fn output_function_testcases(&self, func_info: &FuncTestCaseInfo<'tcx>) -> String{
        let constructor_functions: String = func_info.args.iter()
            .map(|arg| self.make_constuctor_function(arg))
            .collect();
        let mut out = format!("\n#[cfg(test)]\nmod {}_tests {{\n    use super::*;\n\n{}", &func_info.func_name, constructor_functions);

        trace!("Output tests for {}", func_info.func_name);
        for (test_ind, testcase) in func_info.testcases.iter().enumerate(){
            let testcase_str = self.output_testcase(test_ind, func_info, testcase);
            out.push_str(&testcase_str.to_string());
        }

        out.push_str("}\n");
        out
    }

    fn output_internal(&self) -> Result<(), Box<dyn std::error::Error>>{

        std::fs::create_dir_all(&self.test_output_dir)?;
        
        for (func_name, func_info) in self.testcase_map.iter(){
            let function_str = self.output_function_testcases(func_info);

            let mut file = std::fs::File::create(format!("{}/{}_tests.rs", self.test_output_dir, func_name))?;

            write!(file, "{}", function_str)?;
        }   
    
        Ok(())   
    }

    #[logfn_inputs(TRACE)]
    pub fn output(&self){
        debug!("functions: {:?}", self.testcase_map);

        match self.output_internal() {
            Ok(_) => {},
            Err(e) => {error!("test_gen output error: {}", e)}
        };
    }
}