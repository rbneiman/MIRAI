use std::{fmt::{Debug, Formatter}, rc::Rc, collections::HashMap};
use log_derive::logfn_inputs;
use rustc_middle::ty::{Ty, TyCtxt};
use std::io::Write;
use crate::{smt_solver::SmtParam, abstract_value::AbstractValue, type_visitor::TypeVisitor, path::PathEnum};



#[derive(Debug)]
struct ResolvedParam<'tcx>{
    pub ty: Ty<'tcx>,
    pub name: Rc<String>,
    pub type_name: String,
    pub value_string: String,
    pub param_ordinal: Option<usize>,
}

#[derive(Debug)]
struct FuncArg<'tcx>{
    pub ty: Ty<'tcx>,
    pub name: Option<Rc<String>>,
    pub ordinal: usize,
}

#[derive(Debug)]
struct Testcase<'tcx>{
    pub abstract_val: Rc<AbstractValue>,
    pub param_list: Vec<Rc<ResolvedParam<'tcx>>>,
}

#[derive(Debug)]
struct FuncTestCaseInfo<'tcx>{
    pub func_name: Rc<String>,
    pub param_map: HashMap<Rc<String>, Rc<ResolvedParam<'tcx>>>,
    pub testcases: Vec<Testcase<'tcx>>,
    pub args: Vec<FuncArg<'tcx>>,
    pub func_name_raw: Rc<String>,
    // pub arg_types: Vec<Ty<'tcx>>,
    // pub actual_args: Vec<Option<Rc<ResolvedParam<'tcx>>>>,
}

pub struct TestGen<'tcx>{
    test_output_dir: String,
    tcx: TyCtxt<'tcx>,
    testcase_map: HashMap<Rc<String>, FuncTestCaseInfo<'tcx>>,
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
            testcase_map: HashMap::new()
        }
    }

    /// Returns the type of the field with the given ordinal.
    // #[logfn_inputs(TRACE)]
    // pub fn get_field_type(

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
                let name = debug_names.get(&ordinal).map(|v| v.clone());
                
                let func_arg = FuncArg{
                    ty,
                    name,
                    ordinal,
                };
                args.push(func_arg);
            }

            // let func_name_raw = function_name.to_string(),


            self.testcase_map.insert(function_name_filtered.clone(), FuncTestCaseInfo { 
                func_name: function_name_filtered.clone(), 
                param_map: HashMap::new(), 
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

            println!("test_gen name: {:?}, path: {:?}", name, path);

            let resolved = Rc::new(ResolvedParam{
                name,
                ty,
                type_name,
                value_string,
                param_ordinal
            });
            
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

        let mut func_call_param_string = String::new();
        for i in 0..func_info.args.len(){

            if let Some(resolved) = resolved_args[i] {

                func_call_param_string.push_str(format!("{}, ", resolved.value_string).as_str())
            }else{
                let arg = &func_info.args[i];
                let name = arg.name.clone().unwrap_or(Rc::new(format!("param_{}", i+1)));
                
                func_call_param_string.push_str(format!("{}, ", name).as_str())
            }
            
        }
        if func_call_param_string.len() > 1 {
            func_call_param_string.truncate(func_call_param_string.len() - 2);
        }
        

        let func_call_string = format!("{}({});", func_info.func_name_raw, func_call_param_string);
        let out = format!("    #[test]\n    fn test_{}() {{\n{}\n        {}\n    }}\n", test_ind, intializers_string, func_call_string);
        out
    }

    fn output_function_testcases(&self, func_info: &FuncTestCaseInfo<'tcx>) -> String{
        
        let mut out = format!("#[cfg(test)]\nmod {}_tests {{\n    use super::*;\n", &func_info.func_name);

        trace!("Output tests for {}", func_info.func_name);
        for (test_ind, testcase) in func_info.testcases.iter().enumerate(){
            let testcase_str = self.output_testcase(test_ind, func_info, testcase);
            out.push_str(&testcase_str.to_string());
        }

        out.push_str("}");
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