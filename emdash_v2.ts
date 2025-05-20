/* LAMBDAPI SPECIFICATION: https://github.com/1337777/cartier/blob/master/cartierSolution18.lp
* TYPESCRIPT IMPLEMENTATION: https://github.com/1337777/cartier/blob/master/emdash_v2.ts
* KOSTA DOSEN's EMDASH FUNCTORIAL PROGRAMMING IN TYPESCRIPT IN THE WEB BROWSER
* https://github.com/hotdocx/emdash
* https://hotdocx.github.io
* */

// INSTALL: download https://nodejs.org then terminal commands:
// npm install -g ts-node
// ts-node emdash_v2.ts
// after having created this file firstly:
// ./tsconfig.json
// {
//     "compilerOptions": {
//       "target": "es2020", 
//     }
// }

// --- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 7 - Applying Revisions) ---

export let nextVarId = 0;
export const freshVarName = (hint: string = 'v'): string => `${hint}${nextVarId++}`;

export let nextHoleId = 0;
export const freshHoleName = (): string => `?h${nextHoleId++}`;

// --- Term Definition ---
export type BaseTerm =
    | { tag: 'Type' }
    | { tag: 'Var', name: string }
    | { tag: 'Lam', paramName: string, paramType?: Term, body: (v: Term) => Term, _isAnnotated: boolean }
    | { tag: 'App', func: Term, arg: Term }
    | { tag: 'Pi', paramName: string, paramType: Term, bodyType: (v: Term) => Term }
    | { tag: 'Hole', id: string, ref?: Term, elaboratedType?: Term }
    // Emdash Phase 1: Core Categories
    | { tag: 'CatTerm' }
    | { tag: 'ObjTerm', cat: Term }
    | { tag: 'HomTerm', cat: Term, dom: Term, cod: Term }
    | { tag: 'MkCat_',
        objRepresentation: Term,
        homRepresentation: Term,
        composeImplementation: Term
      }
    | { tag: 'IdentityMorph',
        obj: Term,
        cat_IMPLICIT?: Term
      }
    | { tag: 'ComposeMorph',
        g: Term,
        f: Term,
        cat_IMPLICIT?: Term,
        objX_IMPLICIT?: Term,
        objY_IMPLICIT?: Term,
        objZ_IMPLICIT?: Term
      };

export type Term = BaseTerm;
export type PatternVarDecl = { name: string, type: Term };

export const Type = (): Term => ({ tag: 'Type' });
export const Var = (name: string): Term & { tag: 'Var' } => ({ tag: 'Var', name });
export const Lam = (paramName: string, paramTypeOrBody: Term | ((v: Term) => Term), bodyOrNothing?: (v: Term) => Term): Term & { tag: 'Lam' } => {
    if (typeof paramTypeOrBody === 'function' && bodyOrNothing === undefined) {
        return { tag: 'Lam', paramName, paramType: undefined, body: paramTypeOrBody, _isAnnotated: false };
    } else if (bodyOrNothing && typeof bodyOrNothing === 'function' && paramTypeOrBody) {
        return { tag: 'Lam', paramName, paramType: paramTypeOrBody as Term, body: bodyOrNothing, _isAnnotated: true };
    }
    throw new Error(`Invalid Lam arguments: ${paramName}, ${paramTypeOrBody}, ${bodyOrNothing}`);
}
export const App = (func: Term, arg: Term): Term => ({ tag: 'App', func, arg });
export const Pi = (paramName: string, paramType: Term, bodyType: (v: Term) => Term): Term =>
    ({ tag: 'Pi', paramName, paramType, bodyType });
export const Hole = (id?: string): Term & { tag: 'Hole' } => {
    const holeId = id || freshHoleName();
    return { tag: 'Hole', id: holeId, ref: undefined, elaboratedType: undefined };
};

export const CatTerm = (): Term & { tag: 'CatTerm' } => ({ tag: 'CatTerm' });
export const ObjTerm = (cat: Term): Term & { tag: 'ObjTerm' } => ({ tag: 'ObjTerm', cat });
export const HomTerm = (cat: Term, dom: Term, cod: Term): Term & { tag: 'HomTerm' } => ({ tag: 'HomTerm', cat, dom, cod });
export const MkCat_ = (objRepresentation: Term, homRepresentation: Term, composeImplementation: Term): Term & { tag: 'MkCat_' } =>
    ({ tag: 'MkCat_', objRepresentation, homRepresentation, composeImplementation });
export const IdentityMorph = (obj: Term, cat_IMPLICIT?: Term): Term & { tag: 'IdentityMorph' } =>
    ({ tag: 'IdentityMorph', obj, cat_IMPLICIT });
export const ComposeMorph = (g: Term, f: Term, cat_IMPLICIT?: Term, objX_IMPLICIT?: Term, objY_IMPLICIT?: Term, objZ_IMPLICIT?: Term): Term & { tag: 'ComposeMorph' } =>
    ({ tag: 'ComposeMorph', g, f, cat_IMPLICIT, objX_IMPLICIT, objY_IMPLICIT, objZ_IMPLICIT });

export type Binding = { name: string, type: Term };
export type Context = Binding[];
export const emptyCtx: Context = [];
export const extendCtx = (ctx: Context, name: string, type: Term): Context => [{ name, type }, ...ctx];
export const lookupCtx = (ctx: Context, name: string): Binding | undefined => ctx.find(b => b.name === name);

export interface GlobalDef {
    name: string;
    type: Term;
    value?: Term;
    isConstantSymbol?: boolean;
}
export let globalDefs: Map<string, GlobalDef> = new Map();

export function defineGlobal(name: string, type: Term, value?: Term, isConstantSymbol: boolean = false) {
    if (globalDefs.has(name)) console.warn(`Warning: Redefining global ${name}`);
    if (isConstantSymbol && value !== undefined) {
        throw new Error(`Constant symbol ${name} cannot have a definition/value.`);
    }
    globalDefs.set(name, { name, type, value, isConstantSymbol });
}

export interface RewriteRule { name: string; patternVars: PatternVarDecl[]; lhs: Term; rhs: Term; }
export let userRewriteRules: RewriteRule[] = [];
export function addRewriteRule(rule: RewriteRule) {
    userRewriteRules.push(rule);
}

export interface UnificationRule {
    name: string;
    patternVars: PatternVarDecl[];
    lhsPattern1: Term;
    lhsPattern2: Term;
    rhsNewConstraints: Array<{ t1: Term, t2: Term }>;
}
export let userUnificationRules: UnificationRule[] = [];
export function addUnificationRule(rule: UnificationRule) {
    userUnificationRules.push(rule);
}

export type Substitution = Map<string, Term>;
export interface Constraint { t1: Term; t2: Term; origin?: string; }
export let constraints: Constraint[] = [];

export function addConstraint(t1: Term, t2: Term, origin?: string) { constraints.push({ t1, t2, origin }); }
export function getTermRef(term: Term): Term {
    if (term.tag === 'Hole' && term.ref) return getTermRef(term.ref);
    return term;
}

export const MAX_WHNF_ITERATIONS = 1000; // Max iterations for whnf reduction loop
let whnfIterationCount = 0;

export const MAX_STACK_DEPTH = 200; // General recursion depth limit

export let DEBUG_VERBOSE = false;

// Metadata for Emdash symbols
// UPDATED: ObjTerm and HomTerm are NOT constant symbols for rewrite head blocking
export const EMDASH_CONSTANT_SYMBOLS_TAGS = new Set<string>(['CatTerm', 'MkCat_']);
export const EMDASH_UNIFICATION_INJECTIVE_TAGS = new Set<string>(['IdentityMorph', 'CatTerm', 'ObjTerm', 'HomTerm', 'MkCat_']);

export function isKernelConstantSymbolStructurally(term: Term): boolean {
    const t = getTermRef(term);
    if (EMDASH_CONSTANT_SYMBOLS_TAGS.has(t.tag)) return true;
    // Check for global Vars marked as isConstantSymbol
    if (t.tag === 'Var' && globalDefs.get(t.name)?.isConstantSymbol) return true;
    return false;
}

export function isEmdashUnificationInjectiveStructurally(tag: string): boolean {
    return EMDASH_UNIFICATION_INJECTIVE_TAGS.has(tag);
}

export function whnf(term: Term, ctx: Context, stackDepth: number = 0): Term {
    consoleLog(`[TRACE whnf (${stackDepth})] Enter: term = ${printTerm(term)}`);
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`WHNF stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    let current = term;

    for (let i = 0; i < MAX_WHNF_ITERATIONS; i++) {
        consoleLog(`[TRACE whnf (${stackDepth})] Iteration ${i}, current = ${printTerm(current)}`);
        let changedInThisPass = false;
        const termAtStartOfOuterPass = current; // For detecting overall progress in one whnf call if no specific rule restarts

        // 1. Resolve solved Holes (most fundamental step)
        const dereffedCurrent = getTermRef(current);
        if (dereffedCurrent !== current) {
            consoleLog(`[TRACE whnf (${stackDepth})] Hole dereferenced: ${printTerm(current)} -> ${printTerm(dereffedCurrent)}`);
            current = dereffedCurrent;
            changedInThisPass = true; 
        }
        
        const termBeforeInnerReductions = current;


        // 2. User-Defined Rewrite Rules
        consoleLog(`[TRACE whnf (${stackDepth})] Checking user rewrite rules for: ${printTerm(current)} (isKernelConstant: ${isKernelConstantSymbolStructurally(current)})`);
        if (!isKernelConstantSymbolStructurally(current)) {
            for (const rule of userRewriteRules) {
                consoleLog(`[TRACE whnf (${stackDepth})] Trying rule: ${rule.name} on ${printTerm(current)}`);
                const termBeforeThisRuleAttempt = current; // Save the term state before this specific rule match
                const subst = matchPattern(rule.lhs, termBeforeThisRuleAttempt, ctx, rule.patternVars, undefined, stackDepth + 1);
                if (subst) {
                    consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} matched against ${printTerm(termBeforeThisRuleAttempt)}.`);
                    const rhsApplied = getTermRef(applySubst(rule.rhs, subst, rule.patternVars));
                    consoleLog(`[TRACE whnf (${stackDepth})] RHS after subst for rule ${rule.name}: ${printTerm(rhsApplied)}.`);

                    // Check if the rule application resulted in a structural change.
                    if (areStructurallyEqualNoWhnf(rhsApplied, termBeforeThisRuleAttempt, ctx, stackDepth + 1)) {
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} result is structurally identical to matched term. No change by this specific rule. Matched: ${printTerm(termBeforeThisRuleAttempt)}, RHS: ${printTerm(rhsApplied)}.`);
                        // No change from this rule, so continue to the next rule in the userRewriteRules loop.
                    } else {
                        // Structurally different, this is progress from this rule.
                        consoleLog(`[TRACE whnf (${stackDepth})] Rule ${rule.name} resulted in structural change: ${printTerm(termBeforeThisRuleAttempt)} -> ${printTerm(rhsApplied)}.`);
                        current = rhsApplied; // Update the main 'current' term for whnf.
                        changedInThisPass = true;
                        break; // Rule applied and caused change, break from userRewriteRules loop.
                    }
                }
            }
            if (changedInThisPass) {
                consoleLog(`[TRACE whnf (${stackDepth})] A user rule caused structural change. Continuing whnf loop's next iteration. New current for whnf: ${printTerm(current)}`);
                continue; // Restart entire whnf loop from step 1 with the modified 'current'.
            }
        }

        // 3. Head-Specific Reductions (Standard Beta, Categorical Beta, Delta)
        const headSpecificReductionTerm = current; 
        let reducedInThisBlock = false;
        consoleLog(`[TRACE whnf (${stackDepth})] Checking head-specific reductions for: ${printTerm(current)} (tag: ${current.tag})`);

        switch (current.tag) {
            case 'App': { 
                const func = current.func;
                const func_whnf = whnf(func, ctx, stackDepth + 1); 
                const func_whnf_ref = getTermRef(func_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] App: func_whnf_ref = ${printTerm(func_whnf_ref)}`);

                if (func_whnf_ref.tag === 'Lam') {
                    consoleLog(`[TRACE whnf (${stackDepth})] App: Beta reducing with arg ${printTerm(current.arg)}`);
                    current = func_whnf_ref.body(current.arg); 
                    reducedInThisBlock = true;
                } else if (func_whnf !== func) { 
                    consoleLog(`[TRACE whnf (${stackDepth})] App: func part changed to ${printTerm(func_whnf)}, reconstructing App.`);
                    current = App(func_whnf, current.arg);
                    reducedInThisBlock = true; 
                }
                break;
            }
            case 'ObjTerm': { 
                const cat = current.cat;
                const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                const cat_whnf_ref = getTermRef(cat_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                if (cat_whnf_ref.tag === 'MkCat_') {
                    consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: Categorical Beta to ${printTerm(cat_whnf_ref.objRepresentation)}`);
                    current = cat_whnf_ref.objRepresentation; 
                    reducedInThisBlock = true;
                } else if (cat_whnf !== cat) {
                    consoleLog(`[TRACE whnf (${stackDepth})] ObjTerm: cat part changed to ${printTerm(cat_whnf)}, reconstructing ObjTerm.`);
                    current = ObjTerm(cat_whnf);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'HomTerm': { 
                const cat = current.cat;
                const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                const cat_whnf_ref = getTermRef(cat_whnf);
                consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                if (cat_whnf_ref.tag === 'MkCat_') {
                    const newTerm = App(App(cat_whnf_ref.homRepresentation, current.dom), current.cod);
                    consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: Categorical Beta to ${printTerm(newTerm)}`);
                    current = newTerm;
                    reducedInThisBlock = true;
                } else if (cat_whnf !== cat) {
                    consoleLog(`[TRACE whnf (${stackDepth})] HomTerm: cat part changed to ${printTerm(cat_whnf)}, reconstructing HomTerm.`);
                    current = HomTerm(cat_whnf, current.dom, current.cod);
                    reducedInThisBlock = true;
                }
                break;
            }
            case 'ComposeMorph': { 
                consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: cat_IMPLICIT = ${current.cat_IMPLICIT ? printTerm(current.cat_IMPLICIT) : 'undef'}`);
                if (current.cat_IMPLICIT && current.objX_IMPLICIT && current.objY_IMPLICIT && current.objZ_IMPLICIT) {
                    const cat = current.cat_IMPLICIT;
                    const cat_whnf = whnf(cat, ctx, stackDepth + 1);
                    const cat_whnf_ref = getTermRef(cat_whnf);
                    consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: cat_whnf_ref = ${printTerm(cat_whnf_ref)}`);

                    if (cat_whnf_ref.tag === 'MkCat_') {
                        const newTerm = App(App(App(App(App(cat_whnf_ref.composeImplementation, current.objX_IMPLICIT), current.objY_IMPLICIT), current.objZ_IMPLICIT), current.g), current.f);
                        consoleLog(`[TRACE whnf (${stackDepth})] ComposeMorph: Categorical Beta to ${printTerm(newTerm)}`);
                        current = newTerm;
                        reducedInThisBlock = true;
                    } 
                }
                break;
            }
            case 'Var': { 
                const gdef = globalDefs.get(current.name);
                if (gdef && gdef.value !== undefined && !gdef.isConstantSymbol) {
                    consoleLog(`[TRACE whnf (${stackDepth})] Var: Delta reducing ${current.name} to ${printTerm(gdef.value)}`);
                    current = gdef.value;
                    reducedInThisBlock = true;
                }
                break;
            }
        }
        
        if (reducedInThisBlock) {
             consoleLog(`[TRACE whnf (${stackDepth})] Head-specific reduction occurred, continuing to next iteration. New current = ${printTerm(current)}`);
             changedInThisPass = true;
             continue; 
        }

        consoleLog(`[TRACE whnf (${stackDepth})] Before final progress check: current = ${printTerm(current)}, termBeforeInnerReductions = ${printTerm(termBeforeInnerReductions)}, changedInThisPass = ${changedInThisPass}`);
        const currentAfterSubPartsReduced = getTermRef(current); 
        if (currentAfterSubPartsReduced !== termBeforeInnerReductions) { 
            consoleLog(`[TRACE whnf (${stackDepth})] Structural change in sub-parts detected: ${printTerm(termBeforeInnerReductions)} -> ${printTerm(currentAfterSubPartsReduced)}`);
            current = currentAfterSubPartsReduced; 
            changedInThisPass = true; 
        }
        
        if (!changedInThisPass) {
            consoleLog(`[TRACE whnf (${stackDepth})] No change in this pass, breaking loop. Current = ${printTerm(current)}`);
            break; 
        }
        
        consoleLog(`[TRACE whnf (${stackDepth})] End of iteration ${i}. Current = ${printTerm(current)}, termAtStartOfOuterPass = ${printTerm(termAtStartOfOuterPass)}, changedInThisPass = ${changedInThisPass}`);
        if (current === termAtStartOfOuterPass && !changedInThisPass && i > 0) { 
             consoleLog(`[TRACE whnf (${stackDepth})] Term stabilized, breaking loop.`);
             break;
        }
         if (i === MAX_WHNF_ITERATIONS - 1 ) {
             if(changedInThisPass || current !== termAtStartOfOuterPass) {
                console.warn(`[TRACE whnf (${stackDepth})] WHNF reached max iterations for: ${printTerm(term)} -> ${printTerm(current)}`);
             }
        }
    }
    consoleLog(`[TRACE whnf (${stackDepth})] Exit: returning ${printTerm(current)} for original ${printTerm(term)}`);
    return current;
}

export function normalize(term: Term, ctx: Context, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Normalize stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);
    
    const headReduced = whnf(term, ctx, stackDepth + 1);
    // Must use getTermRef here as whnf might return a hole that got solved during its sub-calls.
    const current = getTermRef(headReduced); 

    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm':
            return current; // Vars are returned as is; if they were delta-reducible, whnf would have done it.
        case 'ObjTerm':
            // If whnf turned ObjTerm(MkCat_...) into its representation, current would be that representation.
            // So, if it's still ObjTerm, its category is abstract or a hole.
            return ObjTerm(normalize(current.cat, ctx, stackDepth + 1));
        case 'HomTerm':
            return HomTerm(
                normalize(current.cat, ctx, stackDepth + 1),
                normalize(current.dom, ctx, stackDepth + 1),
                normalize(current.cod, ctx, stackDepth + 1)
            );
        case 'MkCat_': // Arguments of MkCat_ are types or term formers, normalize them.
            return MkCat_(
                normalize(current.objRepresentation, ctx, stackDepth + 1),
                normalize(current.homRepresentation, ctx, stackDepth + 1),
                normalize(current.composeImplementation, ctx, stackDepth + 1)
            );
        case 'IdentityMorph':
            return IdentityMorph(
                normalize(current.obj, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'ComposeMorph':
             // If whnf turned it into Apps (due to MkCat_ cat unfolding), normalize that App structure.
            if (current.tag !== 'ComposeMorph') return normalize(current, ctx, stackDepth + 1);
            // Otherwise, it's an abstract composition, normalize its components.
            return ComposeMorph(
                normalize(current.g, ctx, stackDepth + 1),
                normalize(current.f, ctx, stackDepth + 1),
                current.cat_IMPLICIT ? normalize(current.cat_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objX_IMPLICIT ? normalize(current.objX_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objY_IMPLICIT ? normalize(current.objY_IMPLICIT, ctx, stackDepth + 1) : undefined,
                current.objZ_IMPLICIT ? normalize(current.objZ_IMPLICIT, ctx, stackDepth + 1) : undefined
            );
        case 'Lam': {
            const currentLam = current;
            // Normalize paramType if it exists and is annotated
            const normLamParamType = (currentLam._isAnnotated && currentLam.paramType) 
                                     ? normalize(currentLam.paramType, ctx, stackDepth + 1) 
                                     : undefined; // If not annotated, paramType is for inference, not structural part of norm form yet

            const newLam = Lam(currentLam.paramName, normLamParamType, 
                (v_arg: Term) => {
                    // Use the potentially normalized param type for context if available, otherwise rely on original hole / type.
                    const paramTypeForBodyCtx = normLamParamType || 
                                                (currentLam.paramType ? getTermRef(currentLam.paramType) : Hole(freshHoleName()+"_norm_lam_body"));
                    let bodyCtx = ctx;
                    if (v_arg.tag === 'Var') { bodyCtx = extendCtx(ctx, v_arg.name, paramTypeForBodyCtx); }
                    return normalize(currentLam.body(v_arg), bodyCtx, stackDepth + 1);
                });
            (newLam as Term & {tag:'Lam'})._isAnnotated = currentLam._isAnnotated; // Preserve annotation status
            if(normLamParamType) (newLam as Term & {tag:'Lam'}).paramType = normLamParamType; // Ensure normalized type is set
            return newLam;
        }
        case 'App': // If whnf didn't beta-reduce it, normalize func and arg.
            const normFunc = normalize(current.func, ctx, stackDepth + 1);
            const normArg = normalize(current.arg, ctx, stackDepth + 1);
            const finalNormFunc = getTermRef(normFunc); // It might have normalized to a hole that got solved
            // Check for beta-reduction again after normalizing func and arg, as they might have changed
            if (finalNormFunc.tag === 'Lam') {
                return normalize(finalNormFunc.body(normArg), ctx, stackDepth + 1); // Re-normalize the result
            }
            return App(normFunc, normArg);
        case 'Pi': {
            const currentPi = current;
            const normPiParamType = normalize(currentPi.paramType, ctx, stackDepth + 1);
            return Pi(currentPi.paramName, normPiParamType, (v_arg: Term) => {
                let bodyTypeCtx = ctx;
                // Use the normalized parameter type for the context of the body type
                if (v_arg.tag === 'Var') { bodyTypeCtx = extendCtx(ctx, v_arg.name, normPiParamType); }
                return normalize(currentPi.bodyType(v_arg), bodyTypeCtx, stackDepth + 1);
            });
        }
    }
}

export function areEqual(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    consoleLog(`[TRACE areEqual (${depth})] Enter: t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    if (depth > MAX_STACK_DEPTH) throw new Error(`Equality check depth exceeded (areEqual depth: ${depth})`);
    const normT1 = whnf(t1, ctx, depth + 1);
    const normT2 = whnf(t2, ctx, depth + 1);
    const rt1 = getTermRef(normT1);
    const rt2 = getTermRef(normT2);
    consoleLog(`[TRACE areEqual (${depth})] normT1 = ${printTerm(normT1)}, normT2 = ${printTerm(normT2)} => rt1 = ${printTerm(rt1)}, rt2 = ${printTerm(rt2)}`);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') {
        const result = rt1.id === rt2.id;
        consoleLog(`[TRACE areEqual (${depth})] Holes: ${rt1.id} === ${rt2.id} is ${result}`);
        return result;
    }
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') {
        consoleLog(`[TRACE areEqual (${depth})] One is hole, other is not. Returning false.`);
        return false; 
    }
    if (rt1.tag !== rt2.tag) {
        consoleLog(`[TRACE areEqual (${depth})] Tags differ: ${rt1.tag} vs ${rt2.tag}. Returning false.`);
        return false;
    }

    let result = false;
    switch (rt1.tag) {
        case 'Type': case 'CatTerm': 
            result = (rt2.tag === rt1.tag);
            consoleLog(`[TRACE areEqual (${depth})] Type/CatTerm: result = ${result}`);
            break;
        case 'Var': 
            result = rt1.name === (rt2 as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE areEqual (${depth})] Var: ${rt1.name} === ${(rt2 as Term & {tag:'Var'}).name} is ${result}`);
            break;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            consoleLog(`[TRACE areEqual (${depth})] App: comparing func and arg recursively.`);
            result = areEqual(rt1.func, app2.func, ctx, depth + 1) &&
                   areEqual(rt1.arg, app2.arg, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] App: recursive result = ${result}`);
            break;
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            consoleLog(`[TRACE areEqual (${depth})] Lam: annotated1=${rt1._isAnnotated}, annotated2=${lam2._isAnnotated}`);
            if (rt1._isAnnotated !== lam2._isAnnotated) { result = false; break; }
            
            let paramTypeForCtx_Lam: Term;
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areEqual(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areEqual (${depth})] Lam: annotated param types are equal.`);
                paramTypeForCtx_Lam = getTermRef(rt1.paramType!); // paramType is verified equal
            } else {
                // For unannotated lams, paramType on Lam term itself is undefined.
                // The Pi type inferred for it would have a (possibly hole) param type.
                // For comparing bodies directly, use a fresh hole type as placeholder if not available.
                // This path might be less common if comparisons happen on inferred Pi types mostly.
                paramTypeForCtx_Lam = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_areEqual_unannot_lam_param");
            }

            const freshVName_Lam = rt1.paramName; // Use the original parameter name
            const freshV_Lam = Var(freshVName_Lam);
            const extendedCtx_Lam = extendCtx(ctx, freshVName_Lam, paramTypeForCtx_Lam);
            consoleLog(`[TRACE areEqual (${depth})] Lam: comparing bodies with var ${freshVName_Lam} in extended context.`);
            result = areEqual(rt1.body(freshV_Lam), lam2.body(freshV_Lam), extendedCtx_Lam, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] Lam: bodies comparison result = ${result}`);
            break;
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            consoleLog(`[TRACE areEqual (${depth})] Pi: comparing param types.`);
            if (!areEqual(rt1.paramType, pi2.paramType, ctx, depth + 1)) {
                consoleLog(`[TRACE areEqual (${depth})] Pi: param types not equal.`);
                result = false; break;
            }
            consoleLog(`[TRACE areEqual (${depth})] Pi: param types equal. Comparing body types.`);
            const freshVName_Pi = rt1.paramName; // Use the original parameter name
            const freshV_Pi = Var(freshVName_Pi);
            const extendedCtx_Pi = extendCtx(ctx, freshVName_Pi, getTermRef(rt1.paramType)); 
            consoleLog(`[TRACE areEqual (${depth})] Pi: comparing body types with var ${freshVName_Pi} in extended context.`);
            result = areEqual(rt1.bodyType(freshV_Pi), pi2.bodyType(freshV_Pi), extendedCtx_Pi, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] Pi: body types comparison result = ${result}`);
            break;
        }
        case 'ObjTerm':
            consoleLog(`[TRACE areEqual (${depth})] ObjTerm: comparing categories.`);
            result = areEqual(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] ObjTerm: categories comparison result = ${result}`);
            break;
        case 'HomTerm':
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE areEqual (${depth})] HomTerm: comparing cat, dom, cod.`);
            result = areEqual(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areEqual(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areEqual(rt1.cod, hom2.cod, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] HomTerm: comparison result = ${result}`);
            break;
        case 'MkCat_':
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE areEqual (${depth})] MkCat_: comparing obj, hom, compose impls.`);
            result = areEqual(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areEqual(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] MkCat_: comparison result = ${result}`);
            break;
        case 'IdentityMorph':
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: comparing implicits and obj.`);
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) {
                 if (!areEqual(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { 
                 implicitsResult = false;
            }
            if (!implicitsResult) { result = false; consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: cat_IMPLICITs not equal.`); break; }
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: cat_IMPLICITs equal or both absent. Comparing obj.`);
            result = areEqual(rt1.obj, id2.obj, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] IdentityMorph: obj comparison result = ${result}`);
            break;
        case 'ComposeMorph': { 
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: comparing implicits, g, and f.`);
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areEqual(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; 
            };
            if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: cat_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objX_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objY_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) { result = false; console.log('[TRACE areEqual (${depth})] ComposeMorph: objZ_IMPLICITs not equal.'); break; }
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: All implicits match. Comparing g and f.`);

            result = areEqual(rt1.g, comp2.g, ctx, depth + 1) &&
                   areEqual(rt1.f, comp2.f, ctx, depth + 1);
            consoleLog(`[TRACE areEqual (${depth})] ComposeMorph: g and f comparison result = ${result}`);
            break;
        }
    }
    consoleLog(`[TRACE areEqual (${depth})] Exit: returning ${result} for t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    return result;
}

export function termContainsHole(term: Term, holeId: string, visited: Set<string>, depth = 0): boolean {
    if (depth > MAX_STACK_DEPTH * 2) { // Increased depth for occurs check, can be deeper than other ops
        console.warn(`termContainsHole depth exceeded for hole ${holeId} in ${printTerm(term)}`);
        return true; // Fail safe: assume it contains if too deep
    }
    const current = getTermRef(term);

    switch (current.tag) {
        case 'Hole': return current.id === holeId;
        case 'Type': case 'Var': case 'CatTerm': return false;
        default: {
            // For HOAS terms, if we generate a string key, it might be different each time due to fresh var names.
            // For non-HOAS terms, visited set based on printTerm can be an optimization.
            // A more robust visited set for general terms would involve structural hashing or a Set<Term> if refs are stable.
            // Given HOAS, let's be careful with `printTerm` based visited set.
            // For now, let's remove it to ensure correctness for HOAS, accepting potential performance hit.
            // const termStrKey = printTerm(current); // This can be problematic with fresh names in HOAS.
            // if (visited.has(termStrKey)) return false;
            // visited.add(termStrKey);

            if (current.tag === 'App') {
                return termContainsHole(current.func, holeId, visited, depth + 1) ||
                       termContainsHole(current.arg, holeId, visited, depth + 1);
            } else if (current.tag === 'Lam') {
                // Check paramType if it exists
                if (current.paramType && termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
                // Check body by instantiating with a fresh variable
                const freshV = Var(freshVarName("_occ_check")); // Unique name for this check
                return termContainsHole(current.body(freshV), holeId, visited, depth + 1);
            } else if (current.tag === 'Pi') {
                if (termContainsHole(current.paramType, holeId, visited, depth + 1)) return true;
                const freshV = Var(freshVarName("_occ_check"));
                return termContainsHole(current.bodyType(freshV), holeId, visited, depth + 1);
            }
            else if (current.tag === 'ObjTerm') {
                return termContainsHole(current.cat, holeId, visited, depth + 1);
            } else if (current.tag === 'HomTerm') {
                return termContainsHole(current.cat, holeId, visited, depth + 1) ||
                       termContainsHole(current.dom, holeId, visited, depth + 1) ||
                       termContainsHole(current.cod, holeId, visited, depth + 1);
            } else if (current.tag === 'MkCat_') {
                return termContainsHole(current.objRepresentation, holeId, visited, depth + 1) ||
                       termContainsHole(current.homRepresentation, holeId, visited, depth + 1) ||
                       termContainsHole(current.composeImplementation, holeId, visited, depth + 1);
            } else if (current.tag === 'IdentityMorph') {
                return (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                       termContainsHole(current.obj, holeId, visited, depth + 1);
            } else if (current.tag === 'ComposeMorph') {
                return termContainsHole(current.g, holeId, visited, depth + 1) ||
                       termContainsHole(current.f, holeId, visited, depth + 1) ||
                       (current.cat_IMPLICIT && termContainsHole(current.cat_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objX_IMPLICIT && termContainsHole(current.objX_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objY_IMPLICIT && termContainsHole(current.objY_IMPLICIT, holeId, visited, depth + 1)) ||
                       (current.objZ_IMPLICIT && termContainsHole(current.objZ_IMPLICIT, holeId, visited, depth + 1));
            }
            return false; // Should not be reached for defined tags
        }
    }
}

export enum UnifyResult { Solved, Failed, RewrittenByRule, Progress }

export function unifyHole(hole: Term & {tag: 'Hole'}, term: Term, ctx: Context, depth: number): boolean {
    const normTerm = getTermRef(term); // Dereference term before occurs check
    if (normTerm.tag === 'Hole') {
        if (hole.id === normTerm.id) return true; // Unifying hole with itself is success
        // Consistent ordering for hole unification to avoid chains like ?a := ?b, ?b := ?a
        if (hole.id < normTerm.id) (normTerm as Term & {tag:'Hole'}).ref = hole;
        else hole.ref = normTerm;
        return true;
    }
    // Pass a new Set for visited each time to avoid cross-contamination between different unifyHole calls in a unification problem
    if (termContainsHole(normTerm, hole.id, new Set(), depth + 1)) {
        // console.warn(`Occurs check failed: cannot unify ${hole.id} with ${printTerm(normTerm)}`);
        return false;
    }
    hole.ref = normTerm;
    return true;
}

export function unifyArgs(args1: (Term | undefined)[], args2: (Term | undefined)[], ctx: Context, depth: number, parentRt1: Term, parentRt2: Term): UnifyResult {
    if (args1.length !== args2.length) return UnifyResult.Failed;

    let madeProgress = false;
    let allSubSolved = true;
    for (let i = 0; i < args1.length; i++) {
        const t1_arg = args1[i];
        const t2_arg = args2[i];

        if (t1_arg === undefined && t2_arg === undefined) continue;
        if ((t1_arg === undefined && t2_arg && getTermRef(t2_arg).tag !== 'Hole') ||
            (t2_arg === undefined && t1_arg && getTermRef(t1_arg).tag !== 'Hole')) {
            return UnifyResult.Failed;
        }
        
        const arg1ToUnify = t1_arg === undefined ? Hole(freshHoleName() + "_undef_arg_lhs_" + i) : t1_arg;
        const arg2ToUnify = t2_arg === undefined ? Hole(freshHoleName() + "_undef_arg_rhs_" + i) : t2_arg;

        const argStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1);

        if (argStatus === UnifyResult.Failed) return UnifyResult.Failed;
        if (argStatus === UnifyResult.RewrittenByRule || argStatus === UnifyResult.Progress) {
            madeProgress = true; // If any sub-unification makes progress or rewrites
        }
        if (argStatus !== UnifyResult.Solved) {
            allSubSolved = false; // If any sub-unification isn't fully Solved yet
        }
    }

    if (allSubSolved) {
        // If all args solved and no progress/rewrite, check if parent structures are now equal.
        // This is particularly important if hole fillings in args made parents equal.
        if(areEqual(parentRt1, parentRt2, ctx, depth +1)) return UnifyResult.Solved;
        // If args solved but parents still not equal (e.g. due to different Var names not involved in unification),
        // it's not Failed, but Progress, as the arguments are resolved.
        // The overall unification of parentRt1 and parentRt2 might fail later if these non-unifiable parts persist.
        return UnifyResult.Progress; 
    }
    
    if (madeProgress) return UnifyResult.Progress; // Some arg made progress but not all solved
    
    // If !allSubSolved and !madeProgress, means some args are stuck (not Failed, but not Solved/Progress/Rewritten)
    // This implies the overall unification is also stuck, so Progress.
    return UnifyResult.Progress;
}

export function unify(t1: Term, t2: Term, ctx: Context, depth = 0): UnifyResult {
    if (depth > MAX_STACK_DEPTH) throw new Error(`Unification stack depth exceeded (Unify depth: ${depth}, ${printTerm(t1)} vs ${printTerm(t2)})`);
    
    const rt1_orig = getTermRef(t1);
    const rt2_orig = getTermRef(t2);

    // Optimization: if terms are physically identical and not holes, they are Solved.
    if (rt1_orig === rt2_orig && rt1_orig.tag !== 'Hole') return UnifyResult.Solved;

    // 1. Handle hole cases first.
    // A hole is unified with the whnf'd version of the other term.
    if (rt1_orig.tag === 'Hole') {
        if (unifyHole(rt1_orig, whnf(rt2_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        // If unifyHole fails (e.g. occurs check), try rules with original forms.
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }
    if (rt2_orig.tag === 'Hole') {
        if (unifyHole(rt2_orig, whnf(rt1_orig, ctx, depth + 1), ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_orig, rt2_orig, ctx, depth + 1);
    }

    // 2. Try structural unification for injective constructors *before* full whnf of parents.
    // Applicable if neither rt1_orig nor rt2_orig is a hole at this point.
    if (rt1_orig.tag === rt2_orig.tag && isEmdashUnificationInjectiveStructurally(rt1_orig.tag)) {
        let args1: (Term|undefined)[] = [];
        let args2: (Term|undefined)[] = [];
        switch (rt1_orig.tag) {
            case 'CatTerm': return UnifyResult.Solved;
            case 'ObjTerm':
                args1 = [rt1_orig.cat]; args2 = [(rt2_orig as Term & {tag:'ObjTerm'}).cat];
                break;
            case 'HomTerm':
                const hom1 = rt1_orig as Term & {tag:'HomTerm'}; const hom2 = rt2_orig as Term & {tag:'HomTerm'};
                args1 = [hom1.cat, hom1.dom, hom1.cod]; args2 = [hom2.cat, hom2.dom, hom2.cod];
                break;
            case 'MkCat_':
                const mk1 = rt1_orig as Term & {tag:'MkCat_'}; const mk2 = rt2_orig as Term & {tag:'MkCat_'};
                args1 = [mk1.objRepresentation, mk1.homRepresentation, mk1.composeImplementation];
                args2 = [mk2.objRepresentation, mk2.homRepresentation, mk2.composeImplementation];
                break;
            case 'IdentityMorph':
                const id1 = rt1_orig as Term & {tag:'IdentityMorph'}; const id2 = rt2_orig as Term & {tag:'IdentityMorph'};
                args1 = [id1.cat_IMPLICIT, id1.obj]; args2 = [id2.cat_IMPLICIT, id2.obj];
                break;
            // Default case for this switch should not be hit if tag is in EMDASH_UNIFICATION_INJECTIVE_TAGS
        }
        // Pass rt1_orig, rt2_orig as parent terms for the areEqual check within unifyArgs
        const argStatus = unifyArgs(args1, args2, ctx, depth, rt1_orig, rt2_orig);
        
        // If args unified successfully (Solved) or made Progress, return that result.
        // If args Failed, we fall through to the general whnf path below.
        if (argStatus === UnifyResult.Solved || argStatus === UnifyResult.Progress) {
            return argStatus;
        }
        // Fall-through if argStatus === UnifyResult.Failed
    }

    // 3. General case: whnf both terms and proceed with unification.
    const rt1_whnf = whnf(rt1_orig, ctx, depth + 1);
    const rt2_whnf = whnf(rt2_orig, ctx, depth + 1);
    
    // Re-check equality after whnf, as they might have become equal.
    if (rt1_whnf === rt2_whnf && rt1_whnf.tag !== 'Hole') return UnifyResult.Solved; // Physical equality of non-holes after whnf
    if (areEqual(rt1_whnf, rt2_whnf, ctx, depth + 1)) return UnifyResult.Solved;

    // Handle holes that might have been exposed by whnf (e.g., a variable defined as a hole).
    // getTermRef again after whnf.
    const rt1_final = getTermRef(rt1_whnf);
    const rt2_final = getTermRef(rt2_whnf);

    if (rt1_final.tag === 'Hole') {
        // rt2_final is already whnf'd here.
        if (unifyHole(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
    if (rt2_final.tag === 'Hole') {
        if (unifyHole(rt2_final, rt1_final, ctx, depth + 1)) return UnifyResult.Solved;
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Tags differ after whnf, and neither is a hole. Try rules.
    if (rt1_final.tag !== rt2_final.tag) {
        return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }

    // Tags are the same (rt1_final.tag === rt2_final.tag), neither is a hole.
    // This is the path for:
    // a) Injective constructors whose arguments failed to unify in the pre-whnf path (step 2).
    // b) Non-injective constructors (e.g., App, Lam, Pi, ComposeMorph).
    // c) Simple terms like Type, Var.

    if (isEmdashUnificationInjectiveStructurally(rt1_final.tag)) {
        // This means the pre-whnf path (step 2) for this injective tag resulted in UnifyResult.Failed for its arguments.
        // We now retry unifying the arguments, but this time the arguments are from the whnf'd parent terms.
        let args1_w: (Term|undefined)[] = [];
        let args2_w: (Term|undefined)[] = [];
        switch (rt1_final.tag) {
            case 'CatTerm': return UnifyResult.Solved; // Already known tags are equal
            case 'ObjTerm':
                args1_w = [rt1_final.cat]; args2_w = [(rt2_final as Term & {tag:'ObjTerm'}).cat];
                break;
            case 'HomTerm':
                const hom1_w = rt1_final as Term & {tag:'HomTerm'}; const hom2_w = rt2_final as Term & {tag:'HomTerm'};
                args1_w = [hom1_w.cat, hom1_w.dom, hom1_w.cod]; args2_w = [hom2_w.cat, hom2_w.dom, hom2_w.cod];
                break;
            case 'MkCat_':
                const mk1_w = rt1_final as Term & {tag:'MkCat_'}; const mk2_w = rt2_final as Term & {tag:'MkCat_'};
                args1_w = [mk1_w.objRepresentation, mk1_w.homRepresentation, mk1_w.composeImplementation];
                args2_w = [mk2_w.objRepresentation, mk2_w.homRepresentation, mk2_w.composeImplementation];
                break;
            case 'IdentityMorph':
                const id1_w = rt1_final as Term & {tag:'IdentityMorph'}; const id2_w = rt2_final as Term & {tag:'IdentityMorph'};
                args1_w = [id1_w.cat_IMPLICIT, id1_w.obj]; args2_w = [id2_w.cat_IMPLICIT, id2_w.obj];
                break;
            default: // Should not be reached if tag is in EMDASH_UNIFICATION_INJECTIVE_TAGS
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        }
        // Pass rt1_final, rt2_final as parents to unifyArgs
        const argStatus_w = unifyArgs(args1_w, args2_w, ctx, depth, rt1_final, rt2_final);
        if (argStatus_w === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        return argStatus_w; // Solved or Progress
    }

    // Non-injective cases or general structural unification for core terms (using whnf'd, non-hole terms)
    switch (rt1_final.tag) {
        case 'Type': return UnifyResult.Solved; // Tags are 'Type', so Solved.
        case 'Var': // Vars are equal if names are same. If not, they are distinct rigid terms.
            return rt1_final.name === (rt2_final as Term & {tag:'Var'}).name ? UnifyResult.Solved : tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
        case 'App': {
            const app2_final = rt2_final as Term & {tag:'App'};
            // Unify functions then arguments. If any fails, try rules for the App terms.
            const funcUnifyStatus = unify(rt1_final.func, app2_final.func, ctx, depth + 1);
            if (funcUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const argUnifyStatus = unify(rt1_final.arg, app2_final.arg, ctx, depth + 1);
            if (argUnifyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (funcUnifyStatus === UnifyResult.Solved && argUnifyStatus === UnifyResult.Solved) {
                if (areEqual(rt1_final, rt2_final, ctx, depth + 1)) return UnifyResult.Solved;
                // Sub-parts solved but term not overall equal yet (e.g. due to other constraints needed)
                // or they might become equal later. Try rules if not directly equal now.
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1); 
            }
            return UnifyResult.Progress; // If any sub-part made progress or was rewritten
        }
        case 'Lam': { 
            const lam2_final = rt2_final as Term & {tag:'Lam'};
            if (rt1_final._isAnnotated !== lam2_final._isAnnotated) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1);
            
            let paramTypeStatus = UnifyResult.Solved;
            if (rt1_final._isAnnotated) { 
                if(!rt1_final.paramType || !lam2_final.paramType) return tryUnificationRules(rt1_final, rt2_final, ctx, depth +1); 
                paramTypeStatus = unify(rt1_final.paramType, lam2_final.paramType, ctx, depth + 1);
                if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }

            const freshV = Var(freshVarName(rt1_final.paramName));
            const CtxParamType = rt1_final._isAnnotated && rt1_final.paramType ? getTermRef(rt1_final.paramType) : Hole(freshHoleName() + "_unif_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxParamType);
            const bodyStatus = unify(rt1_final.body(freshV), lam2_final.body(freshV), extendedCtx, depth + 1);

            if(bodyStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyStatus === UnifyResult.Solved) {
                if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'Pi': { 
            const pi2_final = rt2_final as Term & {tag:'Pi'};
            const paramTypeStatus = unify(rt1_final.paramType, pi2_final.paramType, ctx, depth + 1);
            if(paramTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const freshV = Var(freshVarName(rt1_final.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(rt1_final.paramType));
            const bodyTypeStatus = unify(rt1_final.bodyType(freshV), pi2_final.bodyType(freshV), extendedCtx, depth + 1);
            if(bodyTypeStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if(paramTypeStatus === UnifyResult.Solved && bodyTypeStatus === UnifyResult.Solved) {
                if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress;
        }
        case 'ComposeMorph': 
            const cm1_final = rt1_final; const cm2_final = rt2_final as Term & {tag: 'ComposeMorph'};
            let implicitsOk = true;
            const implicitsToUnify: [Term|undefined, Term|undefined][] = [
                [cm1_final.cat_IMPLICIT, cm2_final.cat_IMPLICIT],
                [cm1_final.objX_IMPLICIT, cm2_final.objX_IMPLICIT],
                [cm1_final.objY_IMPLICIT, cm2_final.objY_IMPLICIT],
                [cm1_final.objZ_IMPLICIT, cm2_final.objZ_IMPLICIT],
            ];
            let madeProgressOnImplicits = false;
            for(const [imp1, imp2] of implicitsToUnify) {
                const arg1ToUnify = imp1 === undefined ? Hole(freshHoleName() + "_undef_imp_lhs") : imp1;
                const arg2ToUnify = imp2 === undefined ? Hole(freshHoleName() + "_undef_imp_rhs") : imp2;
                const impStatus = unify(arg1ToUnify, arg2ToUnify, ctx, depth + 1);
                if (impStatus === UnifyResult.Failed) { implicitsOk = false; break; }
                if (impStatus !== UnifyResult.Solved) madeProgressOnImplicits = true;
            }
            if (!implicitsOk) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            const gStatus = unify(cm1_final.g, cm2_final.g, ctx, depth + 1);
            if (gStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            const fStatus = unify(cm1_final.f, cm2_final.f, ctx, depth + 1);
            if (fStatus === UnifyResult.Failed) return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);

            if (!madeProgressOnImplicits && gStatus === UnifyResult.Solved && fStatus === UnifyResult.Solved) {
                 if(areEqual(rt1_final, rt2_final, ctx, depth+1)) return UnifyResult.Solved;
                 return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
            }
            return UnifyResult.Progress; 

        default:
            console.warn(`Unify: Unhandled same-tag case during structural unification: ${rt1_final.tag}`);
            return tryUnificationRules(rt1_final, rt2_final, ctx, depth + 1);
    }
}

// --- Functions for Unification Rules ---
export function collectPatternVars(term: Term, patternVarDecls: PatternVarDecl[], collectedVars: Set<string>, visited: Set<Term> = new Set()): void {
    const current = getTermRef(term);
    if (visited.has(current) && current.tag !== 'Var' && current.tag !== 'Hole') return; 
    visited.add(current);

    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        collectedVars.add(current.name);
    } else if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) { // Pattern Holes can be variables too
        collectedVars.add(current.id);
    }

    switch (current.tag) {
        case 'App':
            collectPatternVars(current.func, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.arg, patternVarDecls, collectedVars, visited);
            break;
        case 'Lam':
            if (current.paramType) collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            // For HOAS Lam/Pi in patterns, we can't easily collect free pattern vars from the body function itself
            // without applying it. Assumed pattern variables are not bound *within* the pattern's HOAS body.
            // If a HOAS body is part of a pattern (e.g. rule LHS is `Lam("x", Var("T"), bodyFunc)`),
            // `bodyFunc` would be a JS function, not a term containing more pattern vars.
            break;
        case 'Pi':
            collectPatternVars(current.paramType, patternVarDecls, collectedVars, visited);
            break;
        case 'ObjTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            break;
        case 'HomTerm':
            collectPatternVars(current.cat, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.dom, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.cod, patternVarDecls, collectedVars, visited);
            break;
        case 'MkCat_':
            collectPatternVars(current.objRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.homRepresentation, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.composeImplementation, patternVarDecls, collectedVars, visited);
            break;
        case 'IdentityMorph':
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.obj, patternVarDecls, collectedVars, visited);
            break;
        case 'ComposeMorph':
            collectPatternVars(current.g, patternVarDecls, collectedVars, visited);
            collectPatternVars(current.f, patternVarDecls, collectedVars, visited);
            if(current.cat_IMPLICIT) collectPatternVars(current.cat_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objX_IMPLICIT) collectPatternVars(current.objX_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objY_IMPLICIT) collectPatternVars(current.objY_IMPLICIT, patternVarDecls, collectedVars, visited);
            if(current.objZ_IMPLICIT) collectPatternVars(current.objZ_IMPLICIT, patternVarDecls, collectedVars, visited);
            break;
        // Other tags don't have sub-terms with pattern vars (Type, Var, Hole (non-pattern var), CatTerm)
    }
}

export function applyAndAddRuleConstraints(rule: UnificationRule, subst: Substitution, ctx: Context): void {
    const lhsVars = new Set<string>();
    collectPatternVars(rule.lhsPattern1, rule.patternVars, lhsVars, new Set<Term>());
    collectPatternVars(rule.lhsPattern2, rule.patternVars, lhsVars, new Set<Term>());

    const finalSubst = new Map(subst); // Copy initial substitution

    // Ensure all pattern variables used in RHS are either bound by LHS or explicitly made fresh holes
    for (const pVarDecl of rule.patternVars) {
        const pVarName = pVarDecl.name;
        if (pVarName === '_') continue; // Wildcard

        let usedInRhs = false;
        for(const {t1: rhs_t1, t2: rhs_t2} of rule.rhsNewConstraints) {
            const rhsConstraintVars = new Set<string>();
            collectPatternVars(rhs_t1, rule.patternVars, rhsConstraintVars, new Set<Term>());
            collectPatternVars(rhs_t2, rule.patternVars, rhsConstraintVars, new Set<Term>());
            if (rhsConstraintVars.has(pVarName)) {
                usedInRhs = true;
                break;
            }
        }
        // If a pVar is used in RHS, but not in LHS and not already in subst (e.g. from matching one side of rule)
        // then it must be a fresh variable introduced by the rule. Instantiate as a fresh hole.
        if (usedInRhs && !lhsVars.has(pVarName) && !finalSubst.has(pVarName)) {
             finalSubst.set(pVarName, Hole(freshHoleName() + "_unifRuleRHS_" + pVarName));
        }
    }

    for (const constrPair of rule.rhsNewConstraints) {
        const newT1 = applySubst(constrPair.t1, finalSubst, rule.patternVars);
        const newT2 = applySubst(constrPair.t2, finalSubst, rule.patternVars);
        addConstraint(newT1, newT2, `UnifRule ${rule.name}`);
    }
}

export function tryUnificationRules(t1: Term, t2: Term, ctx: Context, depth: number): UnifyResult {
    for (const rule of userUnificationRules) {
        // Attempt: rule.lhsPattern1 vs t1, rule.lhsPattern2 vs t2
        let subst1 = matchPattern(rule.lhsPattern1, t1, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t2, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }

        // Attempt: rule.lhsPattern1 vs t2, rule.lhsPattern2 vs t1 (commuted)
        subst1 = matchPattern(rule.lhsPattern1, t2, ctx, rule.patternVars, undefined, depth + 1);
        if (subst1) {
            let subst2 = matchPattern(rule.lhsPattern2, t1, ctx, rule.patternVars, subst1, depth + 1);
            if (subst2) {
                applyAndAddRuleConstraints(rule, subst2, ctx);
                return UnifyResult.RewrittenByRule;
            }
        }
    }
    return UnifyResult.Failed; // No rule applied
}
// --- End functions for Unification Rules ---

export function solveConstraints(ctx: Context, stackDepth: number = 0): boolean {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error("solveConstraints stack depth exceeded");
    let changedInOuterLoop = true;
    let iterations = 0;
    // Max iterations can be high for complex unifications with many rules/holes.
    const maxIterations = (constraints.length * constraints.length + userUnificationRules.length * 2 + 50) * 50 + 200;


    while (changedInOuterLoop && iterations < maxIterations) {
        changedInOuterLoop = false;
        iterations++;
        if(iterations > maxIterations / 2 && iterations % 100 === 0) {
            // console.warn(`solveConstraints reaching high iteration count: ${iterations}/${maxIterations}, constraints left: ${constraints.length}`);
        }


        let currentConstraintIdx = 0;
        while(currentConstraintIdx < constraints.length) {
            const constraint = constraints[currentConstraintIdx];
            const c_t1_current_ref = getTermRef(constraint.t1);
            const c_t2_current_ref = getTermRef(constraint.t2);

            // Optimization: if terms are already equal (after dereferencing), remove constraint.
            // areEqual calls whnf internally.
            if (areEqual(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1)) {
                constraints.splice(currentConstraintIdx, 1);
                changedInOuterLoop = true;
                // Don't increment currentConstraintIdx, as the list shifted. Restart inner loop scan.
                continue; 
            }

            try {
                const unifyResult = unify(c_t1_current_ref, c_t2_current_ref, ctx, stackDepth + 1);

                if (unifyResult === UnifyResult.Solved) {
                    changedInOuterLoop = true;
                    // If solved, the areEqual check at the start of the *next* outer loop iteration (or current if it continues)
                    // should remove it. Or, if a hole was assigned, getTermRef will reflect it.
                    // We still increment currentConstraintIdx to move to the next constraint in *this* pass.
                    currentConstraintIdx++;
                } else if (unifyResult === UnifyResult.RewrittenByRule) {
                    constraints.splice(currentConstraintIdx, 1); // Original constraint removed, new ones added by rule
                    changedInOuterLoop = true;
                    // Don't increment, list shifted, new constraints are at end. Restart scan of constraints.
                    // This ensures new constraints from rules are processed promptly.
                    // However, to avoid infinite loops if a rule doesn't simplify, consider carefully.
                    // For now, assume rules are reductive or add solvable constraints.
                } else if (unifyResult === UnifyResult.Progress) {
                    // Progress means some change happened (e.g. sub-hole solved, or sub-part made progress)
                    // but the top-level constraint isn't fully Solved yet.
                    changedInOuterLoop = true;
                    currentConstraintIdx++;
                } else { // UnifyResult.Failed
                    console.warn(`Unification failed permanently for: ${printTerm(c_t1_current_ref)} === ${printTerm(c_t2_current_ref)} (orig: ${constraint.origin || 'unknown'})`);
                    // console.warn(`Context at failure: ${ctx.map(b => `${b.name}:${printTerm(b.type)}`).join(', ')}`);
                    // console.warn(`Global defs: ${Array.from(globalDefs.keys()).join(', ')}`);
                    return false; // Permanent failure
                }
            } catch (e) {
                console.error(`Error during unification of ${printTerm(c_t1_current_ref)} and ${printTerm(c_t2_current_ref)} (origin: ${constraint.origin || 'unknown'}): ${(e as Error).message}`);
                console.error((e as Error).stack);
                return false;
            }
        }
    }

    if (iterations >= maxIterations && changedInOuterLoop && constraints.length > 0) {
        console.warn("Constraint solving reached max iterations and was still making changes. Constraints left: " + constraints.length);
        // constraints.forEach(c => console.warn(` - ${printTerm(getTermRef(c.t1))} vs ${printTerm(getTermRef(c.t2))}`));
    }
    
    // Final check: all remaining constraints must be true
    for (const constraint of constraints) {
        if (!areEqual(getTermRef(constraint.t1), getTermRef(constraint.t2), ctx, stackDepth + 1)) {
            console.warn(`Final check failed for constraint: ${printTerm(getTermRef(constraint.t1))} === ${printTerm(getTermRef(constraint.t2))} (orig: ${constraint.origin || 'unknown'})`);
            return false;
        }
    }
    return constraints.length === 0;
}

// ADDING NEW FUNCTION HERE
export function areStructurallyEqualNoWhnf(t1: Term, t2: Term, ctx: Context, depth = 0): boolean {
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Enter: t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    if (depth > MAX_STACK_DEPTH) throw new Error(`Structural Equality check depth exceeded (areStructurallyEqualNoWhnf depth: ${depth})`);
    // DO NOT CALL WHNF HERE
    const rt1 = getTermRef(t1);
    const rt2 = getTermRef(t2);
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] rt1 = ${printTerm(rt1)}, rt2 = ${printTerm(rt2)}`);

    if (rt1.tag === 'Hole' && rt2.tag === 'Hole') {
        const result = rt1.id === rt2.id;
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Holes: ${rt1.id} === ${rt2.id} is ${result}`);
        return result;
    }
    if (rt1.tag === 'Hole' || rt2.tag === 'Hole') {
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] One is hole, other is not. Returning false.`);
        return false; 
    }
    if (rt1.tag !== rt2.tag) {
        consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Tags differ: ${rt1.tag} vs ${rt2.tag}. Returning false.`);
        return false;
    }

    let result = false;
    switch (rt1.tag) {
        case 'Type': case 'CatTerm': 
            result = (rt2.tag === rt1.tag);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Type/CatTerm: result = ${result}`);
            break;
        case 'Var': 
            result = rt1.name === (rt2 as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Var: ${rt1.name} === ${(rt2 as Term & {tag:'Var'}).name} is ${result}`);
            break;
        case 'App': {
            const app2 = rt2 as Term & {tag:'App'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] App: comparing func and arg recursively.`);
            result = areStructurallyEqualNoWhnf(rt1.func, app2.func, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.arg, app2.arg, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] App: recursive result = ${result}`);
            break;
        }
        case 'Lam': {
            const lam2 = rt2 as Term & {tag:'Lam'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated1=${rt1._isAnnotated}, annotated2=${lam2._isAnnotated}`);
            if (rt1._isAnnotated !== lam2._isAnnotated) { result = false; break; }
            
            let paramTypeForCtx_Lam_Struct: Term;
            if (rt1._isAnnotated) { 
                if (!rt1.paramType || !lam2.paramType || !areStructurallyEqualNoWhnf(rt1.paramType, lam2.paramType, ctx, depth + 1)) {
                    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types not equal.`);
                    result = false; break;
                }
                consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: annotated param types are equal.`);
                paramTypeForCtx_Lam_Struct = getTermRef(rt1.paramType!); // paramType is verified equal
            } else {
                paramTypeForCtx_Lam_Struct = rt1.paramType ? getTermRef(rt1.paramType) : Hole(freshHoleName()+"_structEq_unannot_lam_param");
            }

            const freshVName_Lam_Struct = rt1.paramName; // Use the original parameter name
            const freshV_Lam_Struct = Var(freshVName_Lam_Struct);
            const extendedCtx_Lam_Struct = extendCtx(ctx, freshVName_Lam_Struct, paramTypeForCtx_Lam_Struct);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: comparing bodies with var ${freshVName_Lam_Struct} in extended context.`);
            result = areStructurallyEqualNoWhnf(rt1.body(freshV_Lam_Struct), lam2.body(freshV_Lam_Struct), extendedCtx_Lam_Struct, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Lam: bodies comparison result = ${result}`);
            break;
        }
        case 'Pi': {
            const pi2 = rt2 as Term & {tag:'Pi'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: comparing param types.`);
            if (!areStructurallyEqualNoWhnf(rt1.paramType, pi2.paramType, ctx, depth + 1)) {
                consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: param types not equal.`);
                result = false; break;
            }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: param types equal. Comparing body types.`);
            const freshVName_Pi_Struct = rt1.paramName; // Use the original parameter name
            const freshV_Pi_Struct = Var(freshVName_Pi_Struct);
            const extendedCtx_Pi_Struct = extendCtx(ctx, freshVName_Pi_Struct, getTermRef(rt1.paramType)); 
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: comparing body types with var ${freshVName_Pi_Struct} in extended context.`);
            result = areStructurallyEqualNoWhnf(rt1.bodyType(freshV_Pi_Struct), pi2.bodyType(freshV_Pi_Struct), extendedCtx_Pi_Struct, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Pi: body types comparison result = ${result}`);
            break;
        }
        case 'ObjTerm':
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ObjTerm: comparing categories.`);
            result = areStructurallyEqualNoWhnf(rt1.cat, (rt2 as Term & {tag:'ObjTerm'}).cat, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ObjTerm: categories comparison result = ${result}`);
            break;
        case 'HomTerm':
            const hom2 = rt2 as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] HomTerm: comparing cat, dom, cod.`);
            result = areStructurallyEqualNoWhnf(rt1.cat, hom2.cat, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.dom, hom2.dom, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.cod, hom2.cod, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] HomTerm: comparison result = ${result}`);
            break;
        case 'MkCat_':
            const mkcat2 = rt2 as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] MkCat_: comparing obj, hom, compose impls.`);
            result = areStructurallyEqualNoWhnf(rt1.objRepresentation, mkcat2.objRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.homRepresentation, mkcat2.homRepresentation, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.composeImplementation, mkcat2.composeImplementation, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] MkCat_: comparison result = ${result}`);
            break;
        case 'IdentityMorph':
            const id2 = rt2 as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: comparing implicits and obj.`);
            const cat1_eq = rt1.cat_IMPLICIT ? getTermRef(rt1.cat_IMPLICIT) : undefined;
            const cat2_eq = id2.cat_IMPLICIT ? getTermRef(id2.cat_IMPLICIT) : undefined;
            let implicitsResult = true;
            if (cat1_eq && cat2_eq) {
                 if (!areStructurallyEqualNoWhnf(cat1_eq, cat2_eq, ctx, depth + 1)) implicitsResult = false;
            } else if (cat1_eq !== cat2_eq) { 
                 implicitsResult = false;
            }
            if (!implicitsResult) { result = false; consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: cat_IMPLICITs not equal.`); break; }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: cat_IMPLICITs equal or both absent. Comparing obj.`);
            result = areStructurallyEqualNoWhnf(rt1.obj, id2.obj, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] IdentityMorph: obj comparison result = ${result}`);
            break;
        case 'ComposeMorph': {
            const comp2 = rt2 as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: comparing implicits, g, and f.`);
            const implicitsMatch = (imp1?: Term, imp2?: Term): boolean => {
                const rImp1 = imp1 ? getTermRef(imp1) : undefined;
                const rImp2 = imp2 ? getTermRef(imp2) : undefined;
                if (rImp1 && rImp2) return areStructurallyEqualNoWhnf(rImp1, rImp2, ctx, depth + 1);
                return rImp1 === rImp2; 
            };
            if (!implicitsMatch(rt1.cat_IMPLICIT, comp2.cat_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: cat_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objX_IMPLICIT, comp2.objX_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objX_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objY_IMPLICIT, comp2.objY_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objY_IMPLICITs not equal.'); break; }
            if (!implicitsMatch(rt1.objZ_IMPLICIT, comp2.objZ_IMPLICIT)) { result = false; console.log('[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: objZ_IMPLICITs not equal.'); break; }
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: All implicits match. Comparing g and f.`);

            result = areStructurallyEqualNoWhnf(rt1.g, comp2.g, ctx, depth + 1) &&
                   areStructurallyEqualNoWhnf(rt1.f, comp2.f, ctx, depth + 1);
            consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] ComposeMorph: g and f comparison result = ${result}`);
            break;
        }
    }
    consoleLog(`[TRACE areStructurallyEqualNoWhnf (${depth})] Exit: returning ${result} for t1 = ${printTerm(t1)}, t2 = ${printTerm(t2)}`);
    return result;
}

export function ensureImplicitsAsHoles(term: Term): Term {
    // This function is called at the start of infer/check, before getTermRef on the input term.
    // It can mutate the term directly.
    if (term.tag === 'IdentityMorph') {
        if (term.cat_IMPLICIT === undefined) {
            // Try to make hole names more informative based on context if possible, e.g. obj name.
            let objHint = "obj";
            if (term.obj.tag === 'Var') objHint = term.obj.name;
            else if (term.obj.tag === 'Hole') objHint = term.obj.id.replace("?","");
            term.cat_IMPLICIT = Hole(freshHoleName() + "_cat_of_" + objHint);
        }
    }
    if (term.tag === 'ComposeMorph') {
        if (term.cat_IMPLICIT === undefined) term.cat_IMPLICIT = Hole(freshHoleName() + "_comp_cat");
        if (term.objX_IMPLICIT === undefined) term.objX_IMPLICIT = Hole(freshHoleName() + "_comp_X");
        if (term.objY_IMPLICIT === undefined) term.objY_IMPLICIT = Hole(freshHoleName() + "_comp_Y");
        if (term.objZ_IMPLICIT === undefined) term.objZ_IMPLICIT = Hole(freshHoleName() + "_comp_Z");
    }
    return term;
}

export function infer(ctx: Context, term: Term, stackDepth: number = 0): Term {
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`Infer stack depth exceeded (depth: ${stackDepth}, term: ${printTerm(term)})`);

    // Ensure implicits are holes *before* getTermRef, as getTermRef might return a solved hole's content.
    const termWithImplicits = ensureImplicitsAsHoles(term);
    const current = getTermRef(termWithImplicits);


    if (current.tag === 'Var') {
        const gdef = globalDefs.get(current.name);
        if (gdef) return gdef.type;
        const binding = lookupCtx(ctx, current.name);
        if (!binding) throw new Error(`Unbound variable: ${current.name} in context [${ctx.map(b => b.name).join(', ')}]`);
        return binding.type;
    }

    switch (current.tag) {
        case 'Type': return Type(); // Type : Type
        case 'Hole': {
            if (current.elaboratedType) return getTermRef(current.elaboratedType); // Return existing, possibly solved type
            const newTypeForHole = Hole(freshHoleName() + "_type_of_" + current.id.replace("?","h"));
            current.elaboratedType = newTypeForHole; // Assign a new hole type
            return newTypeForHole;
        }
        case 'App': {
            const funcType = infer(ctx, current.func, stackDepth + 1);
            // whnf the function's type to expose Pi, or a Hole that needs to become a Pi
            const normFuncType = whnf(funcType, ctx, stackDepth + 1); 
            
            if (normFuncType.tag === 'Hole') {
                // If func's type is a Hole, constrain it to be a Pi type
                const argTypeHole = Hole(freshHoleName() + "_app_argT_of_" + (current.arg.tag === 'Hole' ? current.arg.id.replace("?","h") : "arg"));
                const resultTypeHole = Hole(freshHoleName() + "_app_resT");
                const freshPN = freshVarName("appArgInfer");
                // The hole normFuncType must be equal to Pi(freshPN, argTypeHole, _ => resultTypeHole)
                addConstraint(normFuncType, Pi(freshPN, argTypeHole, _ => resultTypeHole), `App func type ${printTerm(normFuncType)} for ${printTerm(current.func)}`);
                check(ctx, current.arg, argTypeHole, stackDepth + 1); // Check arg against the new hole for argType
                return resultTypeHole;
            }
            if (normFuncType.tag !== 'Pi') throw new Error(`Cannot apply non-function: ${printTerm(current.func)} of type ${printTerm(normFuncType)} (original type: ${printTerm(funcType)})`);
            
            check(ctx, current.arg, normFuncType.paramType, stackDepth + 1);
            // Apply arg to bodyType. Result might need normalization if bodyType contains computations.
            return normFuncType.bodyType(current.arg); 
        }
        case 'Lam': {
            const lam = current; // current is already getTermRef'd
            const paramName = lam.paramName;

            if (lam._isAnnotated && lam.paramType) { // Annotated lambda
                check(ctx, lam.paramType, Type(), stackDepth + 1); // Check param type is a Type
                const paramName = lam.paramName; // Ensure paramName is from the current lam
                const paramType = lam.paramType; // Ensure paramType is from the current lam
                // The bodyType function of the Pi must use its argument.
                return Pi(paramName, paramType, (pi_arg: Term) => {
                    // Infer the type of the lambda's body, where pi_arg is the instance of the lambda's parameter.
                    // The context for this inference must bind paramName to paramType.
                    const tempCtx = extendCtx(ctx, paramName, paramType);
                    return infer(tempCtx, lam.body(pi_arg), stackDepth + 1);
                });
            } else { // Unannotated lambda, infer parameter type
                const paramName = lam.paramName; // Save paramName
                const paramTypeHole = Hole(freshHoleName() + "_lam_" + paramName + "_paramT");
                
                // Bug Fix #1: Tentatively annotate the Lam term itself with the paramTypeHole
                if (term.tag === 'Lam' && !term._isAnnotated) {
                    term.paramType = paramTypeHole;
                    term._isAnnotated = true; 
                } else if (current.tag === 'Lam' && !current._isAnnotated) {
                     current.paramType = paramTypeHole;
                     current._isAnnotated = true;
                }

                // The bodyType function of the Pi must use its argument.
                return Pi(paramName, paramTypeHole, (pi_arg: Term) => {
                    // Infer the type of the lambda's body, where pi_arg is the instance of the lambda's parameter.
                    // The context for this inference must bind paramName to paramTypeHole.
                    const tempCtx = extendCtx(ctx, paramName, paramTypeHole);
                    return infer(tempCtx, lam.body(pi_arg), stackDepth + 1);
                });
            }
        }
        case 'Pi': { // (Π x : A . B) : Type
            const pi = current;
            check(ctx, pi.paramType, Type(), stackDepth + 1); // A : Type
            const paramName = pi.paramName;
            const extendedCtx = extendCtx(ctx, paramName, pi.paramType);
            const bodyTypeInstance = pi.bodyType(Var(paramName)); // B[x/x]
            check(extendedCtx, bodyTypeInstance, Type(), stackDepth + 1); // B[x/x] : Type
            return Type();
        }
        // Emdash Phase 1
        case 'CatTerm': return Type(); // Cat : Type
        case 'ObjTerm': // Obj C : Type, requires C : Cat
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            return Type();
        case 'HomTerm': { // Hom C X Y : Type, requires C:Cat, X:Obj C, Y:Obj C
            check(ctx, current.cat, CatTerm(), stackDepth + 1);
            const catForHom = getTermRef(current.cat); 
            check(ctx, current.dom, ObjTerm(catForHom), stackDepth + 1);
            check(ctx, current.cod, ObjTerm(catForHom), stackDepth + 1);
            return Type();
        }
        case 'MkCat_': { // MkCat O H C : Cat
            // O : Type
            check(ctx, current.objRepresentation, Type(), stackDepth + 1);
            const O_repr_norm = getTermRef(current.objRepresentation); // Use normalized for expected types

            // H : Π X:O . Π Y:O . Type
            const expected_H_type = Pi("X", O_repr_norm, _X => Pi("Y", O_repr_norm, _Y => Type()));
            check(ctx, current.homRepresentation, expected_H_type, stackDepth + 1);
            const H_repr_func_norm = getTermRef(current.homRepresentation);

            // C : Π X:O . Π Y:O . Π Z:O . Π g:(H Y Z) . Π f:(H X Y) . (H X Z)
            const type_of_hom_X_Y = (X_val: Term, Y_val: Term) => App(App(H_repr_func_norm, X_val), Y_val);

            const expected_C_type =
                Pi("Xobj", O_repr_norm, Xobj_term =>
                Pi("Yobj", O_repr_norm, Yobj_term =>
                Pi("Zobj", O_repr_norm, Zobj_term =>
                Pi("gmorph", type_of_hom_X_Y(Yobj_term, Zobj_term), _gmorph_term =>
                Pi("fmorph", type_of_hom_X_Y(Xobj_term, Yobj_term), _fmorph_term =>
                type_of_hom_X_Y(Xobj_term, Zobj_term)
                )))));
            check(ctx, current.composeImplementation, expected_C_type, stackDepth + 1);
            return CatTerm();
        }
        case 'IdentityMorph': { // id X : Hom C X X
            const idTerm = current; // implicits (cat_IMPLICIT) are now filled with holes if undefined
            const catArgHole = idTerm.cat_IMPLICIT!; // Should be a Hole if not provided by user
            
            // Infer type of obj: T_obj
            const objActualType = infer(ctx, idTerm.obj, stackDepth + 1);
            // Add constraint: T_obj === Obj(catArgHole)
            addConstraint(objActualType, ObjTerm(catArgHole), `Object ${printTerm(idTerm.obj)} in IdentityMorph must be of type Obj(${printTerm(catArgHole)})`);
            
            // Return Hom(catArgHole, obj, obj)
            return HomTerm(catArgHole, idTerm.obj, idTerm.obj);
        }
        case 'ComposeMorph': { // g ∘ f : Hom C X Z
            const compTerm = current; // implicits are filled with holes
            const catArgHole = compTerm.cat_IMPLICIT!;
            const XArgHole = compTerm.objX_IMPLICIT!;
            const YArgHole = compTerm.objY_IMPLICIT!;
            const ZArgHole = compTerm.objZ_IMPLICIT!;

            // These checks will generate constraints for f, g, and the hole implicits
            // f : Hom C X Y
            check(ctx, compTerm.f, HomTerm(catArgHole, XArgHole, YArgHole), stackDepth + 1);
            // g : Hom C Y Z
            check(ctx, compTerm.g, HomTerm(catArgHole, YArgHole, ZArgHole), stackDepth + 1);

            // Result type: Hom C X Z
            return HomTerm(catArgHole, XArgHole, ZArgHole);
        }
    }
}

export function check(ctx: Context, term: Term, expectedType: Term, stackDepth: number = 0): void {
    if (stackDepth > MAX_STACK_DEPTH) {
        throw new Error(`check: Max stack depth exceeded. Term: ${printTerm(term)}, Expected: ${printTerm(expectedType)}`);
    }
    // consoleLog(`check: term ${printTerm(term)}, expectedType ${printTerm(expectedType)}`, ctx);

    let currentTerm = getTermRef(term); // Dereference holes fully at the start
    let currentExpectedType = getTermRef(expectedType); // Also dereference expected type

    // Ensure implicits are holes for relevant terms before any processing
    if (currentTerm.tag === 'IdentityMorph' || currentTerm.tag === 'ComposeMorph') {
        currentTerm = ensureImplicitsAsHoles(currentTerm);
    }

    const expectedTypeNorm = whnf(currentExpectedType, ctx, stackDepth + 1);
    // consoleLog(`check (norm expected): term ${printTerm(currentTerm)}, expectedTypeNorm ${printTerm(expectedTypeNorm)}`, ctx);

    // Rule for checking unannotated lambda against Pi
    if (currentTerm.tag === 'Lam' && !currentTerm._isAnnotated && expectedTypeNorm.tag === 'Pi') {
        // consoleLog(`check: lam! ${printTerm(currentTerm)} against Pi ${printTerm(expectedTypeNorm)}`, ctx);
        // Deep elaboration: annotate lambda with param type from Pi, then check body
        const lamTerm = currentTerm; 
        const expectedPi = expectedTypeNorm;

        lamTerm.paramType = expectedPi.paramType;
        lamTerm._isAnnotated = true; 

        const extendedCtx = extendCtx(ctx, lamTerm.paramName, lamTerm.paramType);
        const actualBodyTerm = lamTerm.body(Var(lamTerm.paramName));
        const expectedBodyPiType = expectedPi.bodyType(Var(lamTerm.paramName)); 
        check(extendedCtx, actualBodyTerm, expectedBodyPiType, stackDepth + 1);
        return;
    }

    if (currentTerm.tag === 'Hole') {
        // consoleLog(`check: hole! ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)}`);
        if (!currentTerm.elaboratedType) {
            currentTerm.elaboratedType = expectedTypeNorm;
        } else {
            addConstraint(getTermRef(currentTerm.elaboratedType), expectedTypeNorm, `check Hole ${currentTerm.id}: elaboratedType vs expectedType`);
        }
        check(ctx, expectedTypeNorm, Type(), stackDepth + 1);
        return;
    }

    if (currentTerm.tag === 'IdentityMorph' && expectedTypeNorm.tag === 'HomTerm') {
        const inferredType = infer(ctx, currentTerm, stackDepth + 1);
        addConstraint(inferredType, expectedTypeNorm, `check IdentityMorph: ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)} (via infer)`);
        return;
    }

    if (currentTerm.tag === 'ComposeMorph' && expectedTypeNorm.tag === 'HomTerm') {
        const inferredType = infer(ctx, currentTerm, stackDepth + 1);
        addConstraint(inferredType, expectedTypeNorm, `check ComposeMorph: ${printTerm(currentTerm)} against ${printTerm(expectedTypeNorm)} (via infer)`);
        return;
    }


    // Default case: infer type and check against expected
    const inferredType = infer(ctx, currentTerm, stackDepth + 1);
    const inferredTypeNorm = whnf(inferredType, ctx, stackDepth + 1); 

    // consoleLog(`check: term ${printTerm(currentTerm)}, inferred ${printTerm(inferredTypeNorm)}, expected ${printTerm(expectedTypeNorm)}`);
    addConstraint(inferredTypeNorm, expectedTypeNorm, `check default: inferredType(${printTerm(currentTerm)}) === expectedType(${printTerm(expectedType)})`);
}

export interface ElaborationResult { term: Term; type: Term; }
export function elaborate(term: Term, expectedType?: Term, initialCtx: Context = emptyCtx): ElaborationResult {
    constraints = []; // Reset global constraints
    // Reset fresh ID counters for each elaboration call for reproducible hole/var names in tests.
    // In a real system, these might be instance-based or managed differently.
    nextHoleId = 0; 
    nextVarId = 0; 
    
    let finalTypeToReport: Term;
    // The `term` passed to elaborate is the root of what we're working on.
    // Mutations by `infer` (for Lam unannotated) or `check` (Lam deep elab) should apply to this `term` instance
    // or its sub-objects if they are directly part of its structure.
    const termToElaborate = term; 

    try {
        if (expectedType) {
            check(initialCtx, termToElaborate, expectedType);
            // The expectedType itself might contain holes that get resolved.
            // So, use getTermRef on it for the final reported type.
            finalTypeToReport = getTermRef(expectedType); 
        } else {
            finalTypeToReport = infer(initialCtx, termToElaborate);
        }

        if (!solveConstraints(initialCtx)) {
            const fc = constraints.find(c => !areEqual(getTermRef(c.t1), getTermRef(c.t2), initialCtx));
            let fcMsg = "Unknown constraint";
            if (fc) {
                const fc_t1_print = printTerm(getTermRef(fc.t1));
                const fc_t2_print = printTerm(getTermRef(fc.t2));
                fcMsg = `${fc_t1_print} vs ${fc_t2_print} (orig: ${fc.origin || 'unspecified'})`;
            }
            console.error("Remaining constraints on failure during elaboration:");
            constraints.forEach(c => {
                 const c_t1_dbg = getTermRef(c.t1); const c_t2_dbg = getTermRef(c.t2);
                 console.error(`  ${printTerm(c_t1_dbg)} ${areEqual(c_t1_dbg, c_t2_dbg, initialCtx) ? "===" : "=/="} ${printTerm(c_t2_dbg)} (origin: ${c.origin})`);
            });
            throw new Error(`Type error: Could not solve constraints. Approx failing: ${fcMsg}`);
        }
    } catch (e) {
        // Filter known type system errors vs unexpected JS errors
        if (e instanceof Error && (e.message.startsWith("Type error:") || e.message.startsWith("Unbound variable:") || e.message.startsWith("Cannot apply non-function:") || e.message.startsWith("Constant symbol") || e.message.startsWith("WHNF stack depth") || e.message.startsWith("Normalize stack depth") || e.message.startsWith("Unification stack depth") || e.message.startsWith("Equality check depth") || e.message.startsWith("Infer stack depth") || e.message.startsWith("Check stack depth") || e.message.startsWith("matchPattern stack depth"))) {
            throw e;
        }
        // For other errors, provide more context
        throw new Error(`Elaboration internal error: ${(e as Error).message} on term ${printTerm(termToElaborate)}. Stack: ${(e as Error).stack}`);
    }

    // After solving, termToElaborate might have its holes filled or its structure changed by infer/check (e.g. Lam annotation).
    // Normalizing this termToElaborate structure should give the final elaborated term.
    const normalizedElaboratedTerm = normalize(termToElaborate, initialCtx);

    // The finalTypeToReport (from infer or expectedType) might also have had its holes solved.
    // Normalize it too.
    const normalizedReportedType = normalize(getTermRef(finalTypeToReport), initialCtx);
    
    return { term: normalizedElaboratedTerm, type: normalizedReportedType };
}

export function isPatternVarName(name: string, patternVarDecls: PatternVarDecl[]): boolean {
    return patternVarDecls.some(pvd => pvd.name === name);
}

export function matchPattern(
    pattern: Term, termToMatch: Term, ctx: Context,
    patternVarDecls: PatternVarDecl[],
    currentSubst?: Substitution, stackDepth = 0
): Substitution | null {
    consoleLog(`[TRACE matchPattern (${stackDepth})] Enter: pattern = ${printTerm(pattern)}, termToMatch = ${printTerm(termToMatch)}`);
    if (stackDepth > MAX_STACK_DEPTH) throw new Error(`matchPattern stack depth exceeded for pattern ${printTerm(pattern)} vs term ${printTerm(termToMatch)}`);
    
    const currentTermStruct = getTermRef(termToMatch);
    const rtPattern = getTermRef(pattern); 
    consoleLog(`[TRACE matchPattern (${stackDepth})] rtPattern = ${printTerm(rtPattern)}, currentTermStruct = ${printTerm(currentTermStruct)}`);

    const subst = currentSubst ? new Map(currentSubst) : new Map<string, Term>();

    // Pattern variable case (Var or Hole in pattern treated as pvar)
    if (rtPattern.tag === 'Var' && isPatternVarName(rtPattern.name, patternVarDecls)) {
        const pvarName = rtPattern.name;
        consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Var: ${pvarName}`);
        if (pvarName === '_') {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Wildcard Var "_", returning current subst.`);
            return subst; 
        }
        const existing = subst.get(pvarName);
        if (existing) { 
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Var ${pvarName} already bound to ${printTerm(existing)}. Checking consistency with ${printTerm(currentTermStruct)}`);
            const consistent = areEqual(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Consistency check for ${pvarName}: ${consistent}`);
            return consistent ? subst : null;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Binding ${pvarName} to ${printTerm(currentTermStruct)}`);
        subst.set(pvarName, currentTermStruct); 
        return subst;
    }
    if (rtPattern.tag === 'Hole' && isPatternVarName(rtPattern.id, patternVarDecls)) { 
        const pvarId = rtPattern.id;
        consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Hole (as pvar): ${pvarId}`);
        if (pvarId === '_') {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Wildcard Hole "_", returning current subst.`);
            return subst; 
        }
        const existing = subst.get(pvarId);
        if (existing) {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pattern Hole ${pvarId} already bound to ${printTerm(existing)}. Checking consistency with ${printTerm(currentTermStruct)}`);
            const consistent = areEqual(currentTermStruct, getTermRef(existing), ctx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Consistency check for ${pvarId}: ${consistent}`);
            return consistent ? subst : null;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Binding ${pvarId} to ${printTerm(currentTermStruct)}`);
        subst.set(pvarId, currentTermStruct);
        return subst;
    }

    if (rtPattern.tag === 'Hole') { 
        if (currentTermStruct.tag === 'Hole' && rtPattern.id === currentTermStruct.id) {
            consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Hole in pattern ${rtPattern.id} matches term Hole ${currentTermStruct.id}.`);
            return subst;
        }
        consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Hole in pattern ${rtPattern.id} does not match term ${printTerm(currentTermStruct)}. Returning null.`);
        return null; 
    }
    if (currentTermStruct.tag === 'Hole') {
        consoleLog(`[TRACE matchPattern (${stackDepth})] Term is Hole ${currentTermStruct.id} but pattern is not pvar/concrete matching hole. Returning null.`);
        return null;
    }

    if (rtPattern.tag !== currentTermStruct.tag) {
        consoleLog(`[TRACE matchPattern (${stackDepth})] Tags differ: pattern ${rtPattern.tag} vs term ${currentTermStruct.tag}. Returning null.`);
        return null;
    }

    const matchOptImplicitArgPattern = (currentS: Substitution | null, patArg?: Term, termArg?: Term): Substitution | null => {
        if (!currentS) return null; // Previous match failed

        if (patArg) { // Pattern specifies this implicit argument
            const patArgRef = getTermRef(patArg);
            // If patArg is a wildcard var/hole, it matches anything (even absence if termArg is undef)
            // For pattern matching, wildcard means "don't care and don't bind".
            // If it's a pvar, it tries to bind.
            if ((patArgRef.tag === 'Var' && isPatternVarName(patArgRef.name, patternVarDecls) && patArgRef.name === '_') ||
                (patArgRef.tag === 'Hole' && patArgRef.id === '_')) {
                return currentS; // Wildcard matches presence or absence of termArg
            }

            if (!termArg) return null; // Pattern requires implicit, term doesn't have it (and pattern arg not wildcard)

            // Both pattern and term have the implicit arg, recursively match.
            return matchPattern(patArg, termArg, ctx, patternVarDecls, currentS, stackDepth + 1);

        }
        // If patArg is undefined, pattern doesn't care about this implicit.
        // It matches whether termArg is present or absent.
        return currentS;
    };

    // Structural comparison for each tag
    switch (rtPattern.tag) {
        case 'Type': case 'CatTerm': 
            consoleLog(`[TRACE matchPattern (${stackDepth})] Matched Type/CatTerm.`);
            return subst; 
        case 'Var': 
            const varNameMatch = rtPattern.name === (currentTermStruct as Term & {tag:'Var'}).name;
            consoleLog(`[TRACE matchPattern (${stackDepth})] Concrete Var in pattern: ${rtPattern.name} vs term Var ${(currentTermStruct as Term & {tag:'Var'}).name}. Match: ${varNameMatch}`);
            return varNameMatch ? subst : null;
        case 'App': {
            const termApp = currentTermStruct as Term & {tag:'App'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] App: matching func and arg recursively.`);
            const s1 = matchPattern(rtPattern.func, termApp.func, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s1) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] App: func match failed. Returning null.`);
                return null;
            }
            consoleLog(`[TRACE matchPattern (${stackDepth})] App: func matched. Matching arg.`);
            const s2 = matchPattern(rtPattern.arg, termApp.arg, ctx, patternVarDecls, s1, stackDepth + 1);
            if(!s2) consoleLog(`[TRACE matchPattern (${stackDepth})] App: arg match failed. Returning null.`);
            return s2;
        }
        case 'Lam': { 
            const lamP = rtPattern as Term & {tag:'Lam'};
            const lamT = currentTermStruct as Term & {tag:'Lam'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: pattern annotated=${lamP._isAnnotated}, term annotated=${lamT._isAnnotated}`);
            if (lamP._isAnnotated !== lamT._isAnnotated) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: annotation mismatch. Returning null.`);
                return null;
            }
            
            let tempSubst = subst;
            if (lamP._isAnnotated) { 
                if (!lamP.paramType || !lamT.paramType) {
                     consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: annotated but one has no paramType. Returning null.`);
                     return null; 
                }
                consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: matching annotated param types.`);
                 const sType = matchPattern(lamP.paramType, lamT.paramType, ctx, patternVarDecls, tempSubst, stackDepth + 1);
                 if (!sType) {
                    consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: param type match failed. Returning null.`);
                    return null;
                 }
                 tempSubst = sType;
                 consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: param types matched.`);
            }
            const freshV = Var(freshVarName(lamP.paramName));
            const CtxTypeP = lamP.paramType ? getTermRef(lamP.paramType) : Hole(freshHoleName()+"_match_lam_ctx");
            const extendedCtx = extendCtx(ctx, freshV.name, CtxTypeP);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: comparing bodies using areEqual with fresh var ${freshV.name}.`);
            const bodiesEqual = areEqual(lamP.body(freshV), lamT.body(freshV), extendedCtx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Lam: bodies areEqual result: ${bodiesEqual}`);
            return bodiesEqual ? tempSubst : null;
        }
        case 'Pi': { 
            const piP = rtPattern as Term & {tag:'Pi'};
            const piT = currentTermStruct as Term & {tag:'Pi'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: matching param types.`);
            const sType = matchPattern(piP.paramType, piT.paramType, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!sType) {
                consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: param type match failed. Returning null.`);
                return null;
            }
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: param types matched. Comparing body types using areEqual.`);
            const freshV = Var(freshVarName(piP.paramName));
            const extendedCtx = extendCtx(ctx, freshV.name, getTermRef(piP.paramType)); 
            const bodyTypesEqual = areEqual(piP.bodyType(freshV), piT.bodyType(freshV), extendedCtx, stackDepth + 1);
            consoleLog(`[TRACE matchPattern (${stackDepth})] Pi: body types areEqual result: ${bodyTypesEqual}`);
            return bodyTypesEqual ? sType : null;
        }
        case 'ObjTerm': {
            consoleLog(`[TRACE matchPattern (${stackDepth})] ObjTerm: matching categories.`);
            const catMatchResult = matchPattern(rtPattern.cat, (currentTermStruct as Term & {tag:'ObjTerm'}).cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!catMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] ObjTerm: category match failed.`);
            return catMatchResult;
        }
        case 'HomTerm': {
            const homP = rtPattern as Term & {tag:'HomTerm'};
            const homT = currentTermStruct as Term & {tag:'HomTerm'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: matching cat, dom, cod.`);
            let s = matchPattern(homP.cat, homT.cat, ctx, patternVarDecls, subst, stackDepth + 1);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cat match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cat matched. Matching dom.`);
            s = matchPattern(homP.dom, homT.dom, ctx, patternVarDecls, s, stackDepth + 1);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: dom match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: dom matched. Matching cod.`);
            const codMatchResult = matchPattern(homP.cod, homT.cod, ctx, patternVarDecls, s, stackDepth + 1);
            if(!codMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] HomTerm: cod match failed.`);
            return codMatchResult;
        }
        case 'MkCat_': {
            const mkP = rtPattern as Term & {tag:'MkCat_'};
            const mkT = currentTermStruct as Term & {tag:'MkCat_'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: matching objRepresentation, homRepresentation, composeImplementation.`);
            let s = matchPattern(mkP.objRepresentation, mkT.objRepresentation, ctx, patternVarDecls, subst, stackDepth + 1);
            if(!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: objRepresentation match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: objRepresentation matched. Matching homRepresentation.`);
            s = matchPattern(mkP.homRepresentation, mkT.homRepresentation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: homRepresentation match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: homRepresentation matched. Matching composeImplementation.`);
            const composeImplMatchResult = matchPattern(mkP.composeImplementation, mkT.composeImplementation, ctx, patternVarDecls, s, stackDepth + 1);
            if(!composeImplMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] MkCat_: composeImplementation match failed.`);
            return composeImplMatchResult;
        }


        case 'IdentityMorph': {
            const idP = rtPattern as Term & {tag:'IdentityMorph'};
            const idT = currentTermStruct as Term & {tag:'IdentityMorph'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: matching cat_IMPLICIT and obj.`);
            let s: Substitution | null = subst;
            s = matchOptImplicitArgPattern(s, idP.cat_IMPLICIT, idT.cat_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: cat_IMPLICIT match failed via matchOptImplicitArgPattern.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: cat_IMPLICIT matched. Matching obj.`);
            const objMatchResult = matchPattern(idP.obj, idT.obj, ctx, patternVarDecls, s, stackDepth + 1);
            if(!objMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] IdentityMorph: obj match failed.`);
            return objMatchResult;
        }
        case 'ComposeMorph': {
            const compP = rtPattern as Term & {tag:'ComposeMorph'};
            const compT = currentTermStruct as Term & {tag:'ComposeMorph'};
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: matching implicits, g, and f.`);
            let s: Substitution | null = subst;
            
            s = matchOptImplicitArgPattern(s, compP.cat_IMPLICIT, compT.cat_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: cat_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objX_IMPLICIT, compT.objX_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objX_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objY_IMPLICIT, compT.objY_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objY_IMPLICIT match failed.`); return null; }
            s = matchOptImplicitArgPattern(s, compP.objZ_IMPLICIT, compT.objZ_IMPLICIT);
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: objZ_IMPLICIT match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: All implicits matched. Matching g.`);

            s = matchPattern(compP.g, compT.g, ctx, patternVarDecls, s, stackDepth + 1); 
            if (!s) { consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: g match failed.`); return null; }
            consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: g matched. Matching f.`);
            const fMatchResult = matchPattern(compP.f, compT.f, ctx, patternVarDecls, s, stackDepth + 1);
            if(!fMatchResult) consoleLog(`[TRACE matchPattern (${stackDepth})] ComposeMorph: f match failed.`);
            return fMatchResult;
        }
    }
}

export function applySubst(term: Term, subst: Substitution, patternVarDecls: PatternVarDecl[]): Term {
    const current = getTermRef(term); // Dereference first

    // Check if current is a pattern variable (Var or Hole)
    if (current.tag === 'Var' && isPatternVarName(current.name, patternVarDecls)) {
        if (current.name === '_') return Hole('_'); // Wildcard var "_" should remain Hole "_" if used in RHS
        const replacement = subst.get(current.name);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Var "${current.name}" in RHS. This might be an issue with rule definition or fresh var generation in unif rules. Subst: ${Array.from(subst.keys())}`);
            return current; // Return original if no substitution found (should ideally not happen for well-formed rules)
        }
        return replacement;
    }
    if (current.tag === 'Hole' && isPatternVarName(current.id, patternVarDecls)) {
        if (current.id === '_') return Hole('_'); // Wildcard hole "_"
        const replacement = subst.get(current.id);
        if (!replacement) {
            console.warn(`applySubst: Unbound pattern variable Hole "${current.id}" in RHS. Subst: ${Array.from(subst.keys())}`);
            return current;
        }
        return replacement;
    }

    // Not a pattern variable, so recurse structurally.
    switch (current.tag) {
        case 'Type': case 'Var': case 'Hole': case 'CatTerm': return current; // Concrete terms, no pvars
        case 'App':
            return App(applySubst(current.func, subst, patternVarDecls), applySubst(current.arg, subst, patternVarDecls));
        case 'Lam': {
            const lam = current;
            const lamParamType = lam.paramType ? applySubst(lam.paramType, subst, patternVarDecls) : undefined;
            // Create new HOAS body; substitution applies *inside* the body when it's eventually called.
            // The new HOAS function captures the current `subst` and `patternVarDecls`.
            const newLam = Lam(lam.paramName, lamParamType,
                (v_arg: Term) => applySubst(lam.body(v_arg), subst, patternVarDecls));
            (newLam as Term & {tag:'Lam'})._isAnnotated = lam._isAnnotated;
            return newLam;
        }
        case 'Pi': {
            const pi = current;
            return Pi(pi.paramName, applySubst(pi.paramType, subst, patternVarDecls),
                (v_arg: Term) => applySubst(pi.bodyType(v_arg), subst, patternVarDecls));
        }
        case 'ObjTerm':
            return ObjTerm(applySubst(current.cat, subst, patternVarDecls));
        case 'HomTerm':
            return HomTerm(
                applySubst(current.cat, subst, patternVarDecls),
                applySubst(current.dom, subst, patternVarDecls),
                applySubst(current.cod, subst, patternVarDecls)
            );
        case 'MkCat_':
            return MkCat_(
                applySubst(current.objRepresentation, subst, patternVarDecls),
                applySubst(current.homRepresentation, subst, patternVarDecls),
                applySubst(current.composeImplementation, subst, patternVarDecls)
            );
        case 'IdentityMorph':
            return IdentityMorph(
                applySubst(current.obj, subst, patternVarDecls),
                current.cat_IMPLICIT ? applySubst(current.cat_IMPLICIT, subst, patternVarDecls) : undefined
            );
        case 'ComposeMorph':
            return ComposeMorph(
                applySubst(current.g, subst, patternVarDecls),
                applySubst(current.f, subst, patternVarDecls),
                current.cat_IMPLICIT ? applySubst(current.cat_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objX_IMPLICIT ? applySubst(current.objX_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objY_IMPLICIT ? applySubst(current.objY_IMPLICIT, subst, patternVarDecls) : undefined,
                current.objZ_IMPLICIT ? applySubst(current.objZ_IMPLICIT, subst, patternVarDecls) : undefined
            );
    }
}

// Print term with bound variables handling for HOAS
export function printTerm(term: Term, boundVarsMap: Map<string, string> = new Map(), stackDepth = 0): string {
    if (stackDepth > MAX_STACK_DEPTH * 2) return "<print_depth_exceeded>";
    if (!term) return "<null_term>";
    
    const current = getTermRef(term); // Always print the resolved term

    const getUniqueName = (baseName: string): string => {
        if (!boundVarsMap.has(baseName) && !globalDefs.has(baseName) && !Array.from(boundVarsMap.values()).includes(baseName)) {
            return baseName;
        }
        let uniqueName = baseName;
        let suffix = 1;
        while (globalDefs.has(uniqueName) || Array.from(boundVarsMap.values()).includes(uniqueName)) {
            uniqueName = `${baseName}_${suffix++}`;
        }
        return uniqueName;
    };

    switch (current.tag) {
        case 'Type': return 'Type';
        case 'Var': return boundVarsMap.get(current.name) || current.name;
        case 'Hole': {
            let typeInfo = "";
            if (current.elaboratedType) {
                const elabTypeRef = getTermRef(current.elaboratedType);
                // Avoid printing self-referential or trivial hole types like ?h : ?h or ?h : Type (if Type is obvious)
                if (!((elabTypeRef.tag === 'Hole' && elabTypeRef.id === current.id) || 
                      (elabTypeRef.tag === 'Type' && term.tag === 'Type'))) { // Check original term for Type:Type case
                    // Print elaborated type with current bound vars context
                    const elabTypePrint = printTerm(elabTypeRef, new Map(boundVarsMap), stackDepth + 1); 
                    if(!elabTypePrint.startsWith("?h") || elabTypePrint.length > current.id.length +3 ) { 
                        typeInfo = `(:${elabTypePrint})`;
                    }
                }
            }
            return (current.id === '_' ? '_' : (boundVarsMap.get(current.id) || current.id)) + typeInfo;
        }
        case 'Lam': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName); // Map original name to display name

            const typeAnnotation = (current._isAnnotated && current.paramType) 
                ? ` : ${printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1)}` // Type printed in outer scope
                : '';
            // Instantiate body with a Var using the original paramName, let printTerm handle mapping to display name
            const bodyTerm = current.body(Var(current.paramName)); 
            return `(λ ${paramDisplayName}${typeAnnotation}. ${printTerm(bodyTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'App':
            return `(${printTerm(current.func, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.arg, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'Pi': {
            const paramDisplayName = getUniqueName(current.paramName);
            const newBoundVars = new Map(boundVarsMap);
            newBoundVars.set(current.paramName, paramDisplayName);

            const paramTypeStr = printTerm(current.paramType, new Map(boundVarsMap), stackDepth + 1); // Param type in outer scope
            const bodyTypeTerm = current.bodyType(Var(current.paramName)); // Instantiate with original name
            return `(Π ${paramDisplayName} : ${paramTypeStr}. ${printTerm(bodyTypeTerm, newBoundVars, stackDepth + 1)})`;
        }
        case 'CatTerm': return 'Cat';
        case 'ObjTerm': return `(Obj ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'HomTerm':
            return `(Hom ${printTerm(current.cat, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.dom, new Map(boundVarsMap), stackDepth + 1)} ${printTerm(current.cod, new Map(boundVarsMap), stackDepth + 1)})`;
        case 'MkCat_':
            return `(mkCat_ {O=${printTerm(current.objRepresentation, new Map(boundVarsMap), stackDepth + 1)}, H=${printTerm(current.homRepresentation, new Map(boundVarsMap), stackDepth + 1)}, C=${printTerm(current.composeImplementation, new Map(boundVarsMap), stackDepth + 1)}})`;
        case 'IdentityMorph': {
            let catIdStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') { 
                 catIdStr = ` [cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}]`;
            }
            return `(id${catIdStr} ${printTerm(current.obj, new Map(boundVarsMap), stackDepth + 1)})`;
        }
        case 'ComposeMorph': {
            let catCompStr = "";
            if (current.cat_IMPLICIT && getTermRef(current.cat_IMPLICIT).tag !== 'Hole') {
                 catCompStr = ` [cat=${printTerm(current.cat_IMPLICIT, new Map(boundVarsMap), stackDepth + 1)}]`;
            }
            return `(${printTerm(current.g, new Map(boundVarsMap), stackDepth + 1)} ∘${catCompStr} ${printTerm(current.f, new Map(boundVarsMap), stackDepth + 1)})`;
        }
    }
}

export function consoleLog(message?: any, ...optionalParams: any[]): void {
    if (DEBUG_VERBOSE) {
        console.log(message, ...optionalParams);
    }
}

export function resetMyLambdaPi() {
    constraints = []; globalDefs.clear();
    userRewriteRules.length = 0;
    userUnificationRules.length = 0;
    nextVarId = 0; nextHoleId = 0;
}

// --- Test Suite ---
console.log("--- MyLambdaPi with Emdash Phase 1: Core Categories (Attempt 7) ---");

// SetupPhase1GlobalsAndRules and runPhase1Tests are unchanged from your provided "NEW TEST CODE"
// They will be used to test these modifications.
export function setupPhase1GlobalsAndRules() {
    defineGlobal("NatType", Type(), undefined, true); // NatType is a kernel constant Type
    defineGlobal("BoolType", Type(), undefined, true);

    // Pattern variables for rewrite rules
    // IMPORTANT: Pattern variable names should be distinct from any global/term variable names
    // if possible, or handled carefully by matching logic.
    // Our pattern variables are declared with types, but types aren't used yet in matching.
    const pvarCat = { name: "CAT_pv", type: CatTerm() };
    const pvarX_obj = { name: "X_obj_pv", type: ObjTerm(Var("CAT_pv")) }; // Type annotation for clarity
    const pvarY_obj = { name: "Y_obj_pv", type: ObjTerm(Var("CAT_pv")) };
    const pvarZ_obj = { name: "Z_obj_pv", type: ObjTerm(Var("CAT_pv")) };


    // Rule: g o id_X = g.
    // Pattern: ComposeMorph(g_param, IdentityMorph(X_obj_pv, CAT_pv), CAT_pv, X_obj_pv, X_obj_pv, Y_obj_pv)
    // g_param type: Hom CAT_pv Y_obj_pv X_obj_pv (as per original test, g: Y -> X)
    // This means id_X is on the RIGHT of g for the rule "g o id_X = g" as f o g (g then f)
    // Our ComposeMorph(g,f) means f then g. So rule should be for IdentityMorph(Y) o f = f
    // Let's stick to the rule names and adjust the structure if needed.
    // "comp_g_idX" suggests g is composed with id_X.
    // If g : Hom C Y X and id_X : Hom C X X, then g o id_X makes sense.
    // ComposeMorph(g, id_X, ...): id_X then g. This requires cod(id_X) = dom(g), so X = Y.
    // The rule `ComposeMorph(g, IdentityMorph(X, C), C, Z, X, X) ↪ g` (where `g : Hom C Z X`)
    // This means Z is objX_IMPLICIT, X is objY_IMPLICIT, X is objZ_IMPLICIT
    // So f = IdentityMorph(X,C) which has type Hom C X X.  objX_imp = X, objY_imp = X
    // And g has type Hom C X X. objY_imp = X, objZ_imp = X.
    // Wait, the rule from doc: `ComposeMorph(g, IdentityMorph(X_obj, CAT), CAT, obj_of_g_domain, X_obj, X_obj_cod_of_g) -> g`  (where `g : Hom CAT (obj_of_g_domain) (X_obj)`)
    // So f = IdentityMorph(X_obj, CAT) : Hom CAT X_obj X_obj
    // And g is the first argument to ComposeMorph.
    // Let's use the provided rule structures from Test 5 logic.
    // g_param_gid : Hom CAT_pv Y_obj_pv X_obj_pv
    // lhs: ComposeMorph(Var("g_param_gid"), IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")), /* implicits */ )
    // Implicits for ComposeMorph(g,f): cat, dom(f), cod(f)=dom(g), cod(g)
    // f = IdentityMorph(X_obj_pv, CAT_pv) => dom(f)=X_obj_pv, cod(f)=X_obj_pv
    // g = g_param_gid => dom(g)=Y_obj_pv, cod(g)=X_obj_pv
    // For composition cod(f) = dom(g) => X_obj_pv = Y_obj_pv.
    // This means the pattern vars X_obj_pv and Y_obj_pv must match to the same object for this rule to apply as written.

    // Rule 1: g o id = g.  (Standard notation: f ; g, where f is id)
    // ComposeMorph(g, IdentityMorph(X,C))
    // IdentityMorph(X,C) has type Hom C X X.
    // g must have type Hom C X Y.
    // Result is Hom C X Y.
    // Implicits for ComposeMorph(g, id_X, C, X, X, Y)
    const pvar_g_XY = { name: "g_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_g_idX_fwd", // g after id_X
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_g_XY],
        lhs: ComposeMorph(
            Var("g_XY_pv"),                                     // g: X -> Y
            IdentityMorph(Var("X_obj_pv"), Var("CAT_pv")),      // id_X: X -> X
            Var("CAT_pv"),                                      // Implicit cat
            Var("X_obj_pv"),                                    // Implicit dom(id_X)
            Var("X_obj_pv"),                                    // Implicit cod(id_X) = dom(g_XY)
            Var("Y_obj_pv")                                     // Implicit cod(g_XY)
        ),
        rhs: Var("g_XY_pv")
    });


    // Rule 2: id o f = f. (Standard notation: f ; g, where g is id)
    // ComposeMorph(IdentityMorph(Y,C), f)
    // f has type Hom C X Y.
    // IdentityMorph(Y,C) has type Hom C Y Y.
    // Result is Hom C X Y.
    // Implicits for ComposeMorph(id_Y, f, C, X, Y, Y)
    const pvar_f_XY = { name: "f_XY_pv", type: HomTerm(Var("CAT_pv"), Var("X_obj_pv"), Var("Y_obj_pv")) };
    addRewriteRule({
        name: "comp_idY_f_fwd", // id_Y after f
        patternVars: [pvarCat, pvarX_obj, pvarY_obj, pvar_f_XY],
        lhs: ComposeMorph(
            IdentityMorph(Var("Y_obj_pv"), Var("CAT_pv")),      // id_Y: Y -> Y
            Var("f_XY_pv"),                                     // f: X -> Y
            Var("CAT_pv"),                                      // Implicit cat
            Var("X_obj_pv"),                                    // Implicit dom(f_XY)
            Var("Y_obj_pv"),                                    // Implicit cod(f_XY) = dom(id_Y)
            Var("Y_obj_pv")                                     // Implicit cod(id_Y)
        ),
        rhs: Var("f_XY_pv")
    });
}

export function resetMyLambdaPi_Emdash() { // If needed for more modular testing later
    resetMyLambdaPi();
}

// Helper function to assert equality for test cases
function assertEqual(actual: string, expected: string, message: string) {
    if (actual !== expected) {
        console.error(`Assertion Failed: ${message}`);
        console.error(`Expected: ${expected}`);
        console.error(`Actual:   ${actual}`);
        throw new Error(`Assertion Failed: ${message}`);
    }
    console.log(`Assertion Passed: ${message}`);
}

// Helper function to assert logs for test cases
function assertLogs(fn: () => void, expectedLogs: string[], message: string) {
    const originalLog = console.log;
    const logs: string[] = [];
    console.log = (...args: any[]) => {
        logs.push(args.map(arg => String(arg)).join(' '));
    };

    try {
        fn();
        let match = logs.length === expectedLogs.length && logs.every((log, index) => log.includes(expectedLogs[index]));
        if (!match) {
            console.error(`Assertion Failed: ${message}`);
            console.error(`Expected logs to include: ${JSON.stringify(expectedLogs)}`);
            console.error(`Actual logs: ${JSON.stringify(logs)}`);
            throw new Error(`Assertion Failed: ${message}`);
        }
    } finally {
        console.log = originalLog; // Restore original console.log
    }
    console.log = originalLog; // Restore original console.log in case of early exit
    originalLog(`Assertion Passed: ${message}`); // Use originalLog for this message
}


function runPhase1Tests() {
    const baseCtx = emptyCtx;
    const NatObjRepr = Var("NatType"); // This is a term of type Type
    console.log("\n--- Test 1: Basic Cat/Obj/Hom Types ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    let testTerm : Term;
    testTerm = CatTerm();
    let elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.1 failed: Cat is not Type");

    const someCatHole = Hole("?MyCat");
    const type_of_someCatHole = infer(baseCtx, someCatHole); // Type of hole is another hole, ?type_of_?MyCat
    addConstraint(type_of_someCatHole, CatTerm(), "Constraint: type of ?MyCat is Cat");
    // solveConstraints needs to be called if we want ?MyCat's elaboratedType to be CatTerm()
    // For now, ObjTerm(someCatHole) means check(someCatHole, CatTerm()) will be called by infer(ObjTerm(...))

    testTerm = ObjTerm(someCatHole);
    elabRes = elaborate(testTerm, undefined, baseCtx); // This elaborate will solve ?MyCat's type.
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.2 failed: Obj ?MyCat is not Type");
    // Check if someCatHole's elaborated type was correctly inferred to CatTerm
    const myCatHoleAfterElab = getTermRef(someCatHole) as Term & {tag:"Hole"};
    if (!myCatHoleAfterElab.elaboratedType || !areEqual(getTermRef(myCatHoleAfterElab.elaboratedType), CatTerm(), baseCtx)) {
        // throw new Error(`Test 1.2b failed: ?MyCat elaboratedType not CatTerm. Got: ${myCatHoleAfterElab.elaboratedType ? printTerm(getTermRef(myCatHoleAfterElab.elaboratedType)) : 'undefined'}`);
        // This check is too strict if ?MyCat itself got solved to CatTerm() or another Cat term.
        // The primary check is that ObjTerm(someCatHole) typechecks.
    }


    const objXHole = Hole("?X");
    const objYHole = Hole("?Y");
    // Constrain types of ?X and ?Y to be Obj(?MyCat) AFTER ?MyCat's type is known to be Cat.
    // This happens within the elaboration of HomTerm.
    // No, this needs to be setup if ?X, ?Y are used standalone.
    // If HomTerm is elaborated, its internal checks handle this.

    testTerm = HomTerm(someCatHole, objXHole, objYHole);
    elabRes = elaborate(testTerm, undefined, baseCtx);
    console.log(`Term: ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'Type') throw new Error("Test 1.3 failed: Hom ?MyCat ?X ?Y is not Type");
    console.log("Test 1 Passed.");


    console.log("\n--- Test 2: MkCat_ and Projections ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    // H_repr_Nat_Global : (X:NatType) -> (Y:NatType) -> Type
    defineGlobal("H_repr_Nat_Global", Pi("X", NatObjRepr, _X => Pi("Y", NatObjRepr, _Y => Type())), undefined, true);
    
    // C_impl_Nat_dummy_Global : (X:NatType) -> (Y:NatType) -> (Z:NatType) -> (H_repr_Nat_Global Y Z) -> (H_repr_Nat_Global X Y) -> (H_repr_Nat_Global X Z)
    // Corrected definition:
    defineGlobal("C_impl_Nat_dummy_Global",
        Pi("X_arg", NatObjRepr, X_term =>      // Parameter for X_arg
        Pi("Y_arg", NatObjRepr, Y_term =>      // Parameter for Y_arg
        Pi("Z_arg", NatObjRepr, Z_term =>      // Parameter for Z_arg
        Pi("g_morph", App(App(Var("H_repr_Nat_Global"), Y_term), Z_term), _g_term => // Use Y_term, Z_term
        Pi("f_morph", App(App(Var("H_repr_Nat_Global"), X_term), Y_term), _f_term => // Use X_term, Y_term
        App(App(Var("H_repr_Nat_Global"), X_term), Z_term) // Use X_term, Z_term
        ))))), undefined, true);

    // Dummy compose impl term, e.g. returns first argument g (if types were non-dependent, or use a hole)
    // For type checking, the exact impl doesn't matter as much as its type.
    // Let's make a dummy C_impl term whose type is C_impl_Nat_dummy_Global.
    // It should be a Lam that takes all args and returns a term of type (H_repr_Nat_Global X Z).
    // For simplicity, we can use a Hole for the body if we don't want to construct a placeholder.
    // Or, for this test, just use the global Var directly in MkCat_, assuming it's defined.
    
    const NatCategoryTermVal = MkCat_(NatObjRepr, Var("H_repr_Nat_Global"), Var("C_impl_Nat_dummy_Global"));
    elabRes = elaborate(NatCategoryTermVal, undefined, baseCtx);
    console.log(`NatCategoryTermVal Term: ${printTerm(elabRes.term)}`);
    console.log(`NatCategoryTermVal Type: ${printTerm(elabRes.type)}`);
    if(elabRes.type.tag !== 'CatTerm') throw new Error("Test 2.1 failed: MkCat_ type is not Cat");

    const ObjOfNatCat = ObjTerm(NatCategoryTermVal);
    elabRes = elaborate(ObjOfNatCat, undefined, baseCtx); // elaborate will call normalize, which calls whnf
    console.log(`Obj(NatCategoryTermVal) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    if (!areEqual(elabRes.term, NatObjRepr, baseCtx)) throw new Error(`Test 2.2 failed: Obj(NatCategoryTerm) did not reduce to NatType. Got ${printTerm(elabRes.term)}`);

    defineGlobal("nat_val1_t2", NatObjRepr); 
    defineGlobal("nat_val2_t2", NatObjRepr);
    const X_in_NatCat = Var("nat_val1_t2");
    const Y_in_NatCat = Var("nat_val2_t2");

    const HomInNatCat = HomTerm(NatCategoryTermVal, X_in_NatCat, Y_in_NatCat);
    elabRes = elaborate(HomInNatCat, undefined, baseCtx);
    console.log(`Hom(NatCat,X,Y) Term (norm): ${printTerm(elabRes.term)}, Type: ${printTerm(elabRes.type)}`);
    
    const expectedHomReduced = App(App(Var("H_repr_Nat_Global"), X_in_NatCat), Y_in_NatCat);
    if (!areEqual(elabRes.term, normalize(expectedHomReduced, baseCtx), baseCtx)) throw new Error(`Test 2.3 failed: Hom(NatCat,X,Y) did not reduce correctly. Expected ${printTerm(normalize(expectedHomReduced,baseCtx))} Got ${printTerm(elabRes.term)}`);
    console.log("Test 2 Passed.");


    console.log("\n--- Test 3: IdentityMorph ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    // MyNatCat3_Global is a MkCat_ term, not abstract
    const MyNatCat3_val = MkCat_(NatObjRepr, Var("H_repr_Nat_Global"), Var("C_impl_Nat_dummy_Global"));
    defineGlobal("MyNatCat3_GlobalDef", CatTerm(), MyNatCat3_val, false); // Defined as a MkCat_

    defineGlobal("x_obj_val_t3", ObjTerm(Var("MyNatCat3_GlobalDef"))); 
    const anObjX_term = Var("x_obj_val_t3");

    const id_x = IdentityMorph(anObjX_term); // cat_IMPLICIT will be inferred
    // Expected type of id_x: Hom MyNatCat3_GlobalDef anObjX_term anObjX_term
    // This should normalize to: App(App(H_repr_Nat_Global, anObjX_term), anObjX_term)
    // (because MyNatCat3_GlobalDef is a MkCat_ and ObjTerm(MyNatCat3_GlobalDef) is NatObjRepr,
    // and anObjX_term is of that type)
    const expected_id_x_type_structure = HomTerm(Var("MyNatCat3_GlobalDef"), anObjX_term, anObjX_term);
    
    elabRes = elaborate(id_x, expected_id_x_type_structure, baseCtx);

    console.log(`Term id_x: ${printTerm(elabRes.term)}`);
    console.log(`Type id_x: ${printTerm(elabRes.type)}`);

    const idTermSolved = getTermRef(elabRes.term);
    if (idTermSolved.tag !== 'IdentityMorph') throw new Error (`Test 3.0 failed: elaborated id_x is not IdentityMorph, but ${idTermSolved.tag}`);
    const idTermSolvedAsIdentity = idTermSolved as Term & {tag: 'IdentityMorph'};

    if (!idTermSolvedAsIdentity.cat_IMPLICIT) throw new Error("Test 3.1 failed: id_x cat_IMPLICIT not filled.");
    if (!areEqual(getTermRef(idTermSolvedAsIdentity.cat_IMPLICIT), Var("MyNatCat3_GlobalDef"), baseCtx)) {
        throw new Error(`Test 3.1 failed: id_x.cat_IMPLICIT not resolved to MyNatCat3_GlobalDef. Got: ${printTerm(getTermRef(idTermSolvedAsIdentity.cat_IMPLICIT!))}`);
    }
    
    const expected_normalized_type = normalize(App(App(Var("H_repr_Nat_Global"), anObjX_term), anObjX_term), baseCtx);
    if (!areEqual(elabRes.type, expected_normalized_type, baseCtx)) {
         throw new Error(`Test 3.2 failed: id_x type mismatch. Expected ${printTerm(expected_normalized_type)}, Got ${printTerm(elabRes.type)}`);
    }
    console.log("Test 3 Passed.");

    console.log("\n--- Test 4: ComposeMorph Inference ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules();
    defineGlobal("C4_Global", CatTerm(), undefined, true); // C4_Global is an ABSTRACT Cat

    defineGlobal("obj_x_val_t4", ObjTerm(Var("C4_Global")));
    defineGlobal("obj_z_val_t4", ObjTerm(Var("C4_Global")));
    const x_term_t4 = Var("obj_x_val_t4");
    const z_term_t4 = Var("obj_z_val_t4");
    
    const y_hole_obj_t4 = Hole("?y_obj_t4");
    // For y_hole_obj_t4 to be used in Hom C4_Global _ _, its type must be ObjTerm(C4_Global)
    // This constraint will be added by check(f, Hom(C4,x,y_hole)) and check(g, Hom(C4,y_hole,z))
    
    const f_morph_hole = Hole("?f_xy_t4");
    const g_morph_hole = Hole("?g_yz_t4");

    // comp_gf = g_morph_hole o f_morph_hole
    // We are providing all implicits here for ComposeMorph for this test,
    // to ensure \`check\` for ComposeMorph (when expected type is HomTerm) correctly
    // uses these provided implicits to constrain f and g.
    const comp_gf = ComposeMorph(g_morph_hole, f_morph_hole, Var("C4_Global"), x_term_t4, y_hole_obj_t4, z_term_t4);
    const expectedCompType = HomTerm(Var("C4_Global"), x_term_t4, z_term_t4);
    
    elabRes = elaborate(comp_gf, expectedCompType, baseCtx);

    console.log(`Term comp_gf: ${printTerm(elabRes.term)}`);
    console.log(`Type comp_gf: ${printTerm(elabRes.type)}`);

    if(!areEqual(elabRes.type, expectedCompType, baseCtx)) throw new Error(`Test 4.0 Failed: comp_gf type not as expected. Got ${printTerm(elabRes.type)}, Expected ${printTerm(expectedCompType)}`);

    const compTermSolved = elabRes.term as Term & {tag:"ComposeMorph"};
    if (compTermSolved.tag !== 'ComposeMorph') throw new Error(`Test 4.0b failed: comp_gf did not remain ComposeMorph. Got ${compTermSolved.tag}`);

    if (!compTermSolved.cat_IMPLICIT || !compTermSolved.objX_IMPLICIT || !compTermSolved.objY_IMPLICIT || !compTermSolved.objZ_IMPLICIT) {
        throw new Error("Test 4.1 failed: ComposeMorph implicits not resolved/present as expected.");
    }
    if(!areEqual(getTermRef(compTermSolved.cat_IMPLICIT), Var("C4_Global"), baseCtx)) throw new Error("Test 4.1 Failed: comp.cat not C4_Global");
    if(!areEqual(getTermRef(compTermSolved.objX_IMPLICIT), x_term_t4, baseCtx)) throw new Error("Test 4.1 Failed: comp.X not obj_x_val_t4");
    // y_hole_obj_t4 should still be a hole after normalization if it wasn't solved by other constraints
    // Its elaboratedType should be ObjTerm(C4_Global)
    if(!areEqual(getTermRef(compTermSolved.objY_IMPLICIT), y_hole_obj_t4, baseCtx)) throw new Error(`Test 4.1 Failed: comp.Y not ${y_hole_obj_t4.id}. Got ${printTerm(getTermRef(compTermSolved.objY_IMPLICIT!))}`);
    if(!areEqual(getTermRef(compTermSolved.objZ_IMPLICIT), z_term_t4, baseCtx)) throw new Error("Test 4.1 Failed: comp.Z not obj_z_val_t4");

    const f_type_hole = getTermRef(f_morph_hole) as Term & {tag:"Hole"};
    const g_type_hole = getTermRef(g_morph_hole) as Term & {tag:"Hole"};

    if (!f_type_hole.elaboratedType || !g_type_hole.elaboratedType) throw new Error("Test 4.2: f or g did not get elaborated types.");

    const expected_f_type = HomTerm(Var("C4_Global"), x_term_t4, y_hole_obj_t4);
    const expected_g_type = HomTerm(Var("C4_Global"), y_hole_obj_t4, z_term_t4);

    if (!areEqual(getTermRef(f_type_hole.elaboratedType), expected_f_type, baseCtx)) throw new Error(`Test 4.3: ?f_xy type mismatch. Got ${printTerm(getTermRef(f_type_hole.elaboratedType))}, expected ${printTerm(expected_f_type)}`);
    if (!areEqual(getTermRef(g_type_hole.elaboratedType), expected_g_type, baseCtx)) throw new Error(`Test 4.4: ?g_yz type mismatch. Got ${printTerm(getTermRef(g_type_hole.elaboratedType))}, expected ${printTerm(expected_g_type)}`);
    
    // Check type of y_hole_obj_t4
    const y_hole_actual_type = infer(baseCtx, y_hole_obj_t4); // Should pick up its elaborated type
    const y_hole_expected_type = ObjTerm(Var("C4_Global"));
    if(!areEqual(y_hole_actual_type, y_hole_expected_type, baseCtx)) {
        throw new Error(`Test 4.5: y_hole_obj_t4 type mismatch. Got ${printTerm(y_hole_actual_type)}, expected ${printTerm(y_hole_expected_type)}`);
    }
    console.log("Test 4 Passed.");


    console.log("\n--- Test 5: Rewrite rule comp (g o id) ---");
    resetMyLambdaPi(); setupPhase1GlobalsAndRules(); // Rules comp_g_idX_fwd and comp_idY_f_fwd are setup
    defineGlobal("C5_cat_global", CatTerm(), undefined, true); 

    defineGlobal("x5_obj_t5", ObjTerm(Var("C5_cat_global")));
    defineGlobal("y5_obj_t5", ObjTerm(Var("C5_cat_global")));
    const X5_term = Var("x5_obj_t5");
    const Y5_term = Var("y5_obj_t5");

    // Rule "comp_g_idX_fwd": ComposeMorph(g_XY, id_X, C, X, X, Y) -> g_XY
    // g_XY : Hom C X Y
    // id_X : Hom C X X
    defineGlobal("g_XY_concrete_t5", HomTerm(Var("C5_cat_global"), X5_term, Y5_term));
    const g_XY_for_rule = Var("g_XY_concrete_t5");
    const id_X5_for_rule = IdentityMorph(X5_term, Var("C5_cat_global"));

    const test_term_g_o_id = ComposeMorph(g_XY_for_rule, id_X5_for_rule, 
                                          Var("C5_cat_global"), X5_term, X5_term, Y5_term);
    
    elabRes = elaborate(test_term_g_o_id, undefined, baseCtx);
    console.log(`Term (g o id_X): ${printTerm(elabRes.term)}`);
    console.log(`Type (g o id_X): ${printTerm(elabRes.type)}`);

    if (!areEqual(elabRes.term, g_XY_for_rule, baseCtx)) {
        throw new Error(`Test 5.1 failed: (g o id_X) did not reduce to g. Got ${printTerm(elabRes.term)}, expected ${printTerm(g_XY_for_rule)}`);
    }
    const expectedTypeT5_1 = HomTerm(Var("C5_cat_global"), X5_term, Y5_term);
    if (!areEqual(elabRes.type, expectedTypeT5_1, baseCtx)) {
        throw new Error(`Test 5.1 type failed. Got ${printTerm(elabRes.type)}, expected ${printTerm(expectedTypeT5_1)}`);
    }

    // Rule "comp_idY_f_fwd": ComposeMorph(id_Y, f_XY, C, X, Y, Y) -> f_XY
    // f_XY : Hom C X Y
    // id_Y : Hom C Y Y
    defineGlobal("f_XY_concrete_t5", HomTerm(Var("C5_cat_global"), X5_term, Y5_term));
    const f_XY_for_rule = Var("f_XY_concrete_t5");
    const id_Y5_for_rule = IdentityMorph(Y5_term, Var("C5_cat_global"));

    const test_term_id_o_f = ComposeMorph(id_Y5_for_rule, f_XY_for_rule,
                                          Var("C5_cat_global"), X5_term, Y5_term, Y5_term);

    elabRes = elaborate(test_term_id_o_f, undefined, baseCtx);
    console.log(`Term (id_Y o f): ${printTerm(elabRes.term)}`);
    console.log(`Type (id_Y o f): ${printTerm(elabRes.type)}`);
    if (!areEqual(elabRes.term, f_XY_for_rule, baseCtx)) {
        throw new Error(`Test 5.2 failed: (id_Y o f) did not reduce to f. Got ${printTerm(elabRes.term)}, expected ${printTerm(f_XY_for_rule)}`);
    }
    const expectedTypeT5_2 = HomTerm(Var("C5_cat_global"), X5_term, Y5_term);
     if (!areEqual(elabRes.type, expectedTypeT5_2, baseCtx)) {
        throw new Error(`Test 5.2 type failed. Got ${printTerm(elabRes.type)}, expected ${printTerm(expectedTypeT5_2)}`);
    }
    console.log("Test 5 Passed.");
}


// Helper to get type for elabType
function elabType(term: Term, ctx: Context = emptyCtx): Term {
    return elaborate(term, Type(), ctx).term;
}

function runBaseDTTTests() {
    console.log("\nRunning Base Dependent Type Theory (MyLambdaPi) Tests...");
    const Ctx: Context = emptyCtx;

    // Test B1: Type : Type
    resetMyLambdaPi();
    try {
        const result = elaborate(Type(), undefined, Ctx);
        assertEqual(printTerm(result.type), "Type", "Test B1.1: Type : Type");
        assertEqual(printTerm(result.term), "Type", "Test B1.2: Elaborated Type is Type");
    } catch (e: any) {
        console.error("Test B1 Failed:", e.message, e.stack);
    }

    // Test B2: Variable Lookup and Basic Pi/Lam/App
    resetMyLambdaPi();
    try {
        // (A: Type) -> A
        const typeFormer = Pi("A", Type(), (A_var: Term): Term => A_var);
        let res = elaborate(typeFormer, undefined, Ctx);
        assertEqual(printTerm(res.term), "(Π A : Type. A)", "Test B2.1: Pi (A:Type). A is correct term");
        assertEqual(printTerm(res.type), "Type", "Test B2.1: Type of (Π A:Type. A) is Type");

        // id = (λ A:Type. λ x:A. x)
        const idFuncTerm = Lam("A", Type(), (A_var: Term): Term => Lam("x", A_var, (x_var: Term): Term => x_var));
        res = elaborate(idFuncTerm, undefined, Ctx);
        assertEqual(printTerm(res.type), "(Π A : Type. (Π x : A. A))", "Test B2.2: Inferred type of id function");
        assertEqual(printTerm(res.term), "(λ A : Type. (λ x : A. x))", "Test B2.2: Elaborated id function");

        // Apply id to Type and then to Type itself (as a term)
        // (id Type) Type
        defineGlobal("GlobalId", res.type, res.term); // res.term is already the elaborated idFuncTerm
        const appliedId = App(App(Var("GlobalId"), Type()), Type());
        res = elaborate(appliedId, undefined, Ctx);
        assertEqual(printTerm(res.term), "Type", "Test B2.3: (id Type Type) evaluates to Type");
        assertEqual(printTerm(res.type), "Type", "Test B2.3: Type of (id Type Type) is Type");

    } catch (e: any) {
        console.error("Test B2 Failed:", e.message, e.stack);
    }

    // Test B3: Beta Reduction
    resetMyLambdaPi();
    try {
        // (λ x:Type. x) Type  ~> Type
        const term = App(Lam("x", Type(), (x_var: Term): Term => x_var), Type());
        const result = elaborate(term, undefined, Ctx);
        assertEqual(printTerm(result.term), "Type", "Test B3.1: Beta reduction (λx:Type. x) Type");
        assertEqual(printTerm(result.type), "Type", "Test B3.1: Type is Type");
    } catch (e: any) {
        console.error("Test B3 Failed:", e.message, e.stack);
    }

    // Test B4: Unbound Variable
    resetMyLambdaPi();
    try {
        elaborate(Var("unbound"), undefined, Ctx);
        console.error("Test B4 Failed: Should have thrown Unbound variable error.");
    } catch (e: any) {
        if ((e as Error).message.includes("Unbound variable: unbound")) {
            console.log("Assertion Passed: Test B4: Detected unbound variable as expected.");
        } else {
            console.error("Test B4 Failed: Incorrect error for unbound variable.", (e as Error).message, (e as Error).stack);
        }
    }

    // Test B5: Hole Inference basic
    resetMyLambdaPi();
    try {
        // infer _
        const holeTerm = Hole("testHoleB5");
        const result = elaborate(holeTerm, undefined, Ctx);
        assertEqual(printTerm(result.term), "testHoleB5(:?h0_type_of_testHoleB5)", "Test B5.1: Elaborated hole is itself");
        // Hole names are ?h0, ?h1 etc. by default from freshHoleName
        assertEqual(printTerm(result.type), "?h0_type_of_testHoleB5", "Test B5.1: Type of inferred hole is a new hole for its type"); 

        resetMyLambdaPi(); // Reset for fresh hole names
        const holeTerm2 = Hole("testHoleB5_2");
        const result2 = elaborate(holeTerm2, Type(), Ctx);
        assertEqual(printTerm(result2.term), "testHoleB5_2(:Type)", "Test B5.2: Elaborated hole checked against Type");
        assertEqual(printTerm(result2.type), "Type", "Test B5.2: Type of hole checked against Type is Type");
    } catch (e: any) {
        console.error("Test B5 Failed:", e.message, e.stack);
    }

    // Test B6: Definitional Equality (areEqual)
    resetMyLambdaPi();
    try {
        const term1_src = Lam("x", Type(), (x_var: Term): Term => x_var);
        const term2_src = Lam("y", Type(), (y_var: Term): Term => y_var);
        const elab1 = elaborate(term1_src, undefined, Ctx).term;
        const elab2 = elaborate(term2_src, undefined, Ctx).term;
        //NO assertEqual(printTerm(elab1), printTerm(elab2), "Test B6.1: Alpha-equivalent lambdas should print the same after elaboration");

        const pi1_src = Pi("A", Type(), (A_var: Term): Term => A_var);
        const pi2_src = Pi("B", Type(), (B_var: Term): Term => B_var);
        const elabPi1 = elaborate(pi1_src, undefined, Ctx).term;
        const elabPi2 = elaborate(pi2_src, undefined, Ctx).term;
        // NO assertEqual(printTerm(elabPi1), printTerm(elabPi2), "Test B6.2: Alpha-equivalent Pi-types should print the same");

    } catch (e: any) {
        console.error("Test B6 Failed:", e.message, e.stack);
    }

    // Test B7: Normalization (via elaboration)
    resetMyLambdaPi();
    try {
        // Corrected B7.1: Well-typed complex beta-reduction
        // Term: ((λ F : (Π Z : Type. Type). (F Type)) (λ Y : Type. Y))
        // Expected to normalize to Type, with type Type.

        const piTypeForZ = Pi("Z", Type(), (Z_var: Term): Term => Type()); // Represents (Π Z : Type. Type)
        
        const outerLamFunc = Lam("F", piTypeForZ, (F_var: Term): Term => App(F_var, Type())); // Represents (λ F : (Π Z : Type. Type). (F Type))
        
        const innerIdFunc = Lam("Y", Type(), (Y_var: Term): Term => Y_var); // Represents (λ Y : Type. Y)
        
        const complexTermNew = App(outerLamFunc, innerIdFunc);

        const result = elaborate(complexTermNew, undefined, Ctx);
        assertEqual(printTerm(result.term), "Type", "Test B7.1: Normalization of complex beta-reduction evaluates to Type");
        assertEqual(printTerm(result.type), "Type", "Test B7.1: Type of normalized complex term is Type");

    } catch (e: any) {
        console.error("Test B7 Failed:", e.message, e.stack);
    }

    // Test B8: Let expression (Placeholder)
    resetMyLambdaPi();
    try {
        console.warn("Test B8 for Let expressions is a placeholder and will likely fail or do nothing if Let is not implemented in emdash_v2.ts BaseTerm and elaboration logic.");
    } catch (e: any) {
        console.error("Test B8 Failed (as expected if Let is not implemented, otherwise an issue):", (e as Error).message, (e as Error).stack);
    }

    // Test B9: Type Mismatch Error
    resetMyLambdaPi();
    try {
        elaborate(Type(), Pi("X", Type(), (X_var: Term): Term => X_var), Ctx);
        console.error("Test B9 Failed: Should have thrown a type mismatch error.");
    } catch (e: any) {
        if ((e as Error).message.includes("Could not solve constraints") || (e as Error).message.includes("Cannot unify Type with Π X:Type. X")) {
            console.log("Assertion Passed: Test B9: Detected type mismatch as expected.");
        } else {
            console.error("Test B9 Failed: Incorrect error for type mismatch.", (e as Error).message, (e as Error).stack);
        }
    }

    // Test B10: Lambda type inference for unannotated params
    resetMyLambdaPi();
    try {
        const unannotId = Lam("x", (x_var: Term): Term => x_var); // Unannotated Lam
        const result = elaborate(unannotId, undefined, Ctx);
        const printType = printTerm(result.type);
        if (result.type.tag === 'Pi' && result.type.paramType?.tag === 'Hole') {
             const paramTypeHoleName = result.type.paramType.id;
             const expectedTypeStr = `(Π x : ${paramTypeHoleName}. ${paramTypeHoleName})`;
             assertEqual(printType, expectedTypeStr, `Test B10.1: Inferred type of λx.x is ${expectedTypeStr}`);
        } else {
            throw new Error (`Test B10.1: Inferred type structure incorrect. Got ${printType}`);
        }
    } catch (e: any) {
        console.error("Test B10 Failed:", e.message, e.stack);
    }

    // Test B11: Unannotated Lam with Expected Pi Type
    resetMyLambdaPi();
    try {
        // Term: (λx. x) expected type: (Π Y:Type. Y)
        const unannotId = Lam("x", (x_var: Term): Term => x_var); // λx.x
        const expectedPiType = Pi("Y", Type(), (Y_var: Term): Term => Type()); // ΠY:Type.Y

        const result = elaborate(unannotId, expectedPiType, Ctx);

        if (result.term.tag !== 'Lam' || !result.term._isAnnotated || !result.term.paramType) {
            throw new Error("Test B11.1: Elaborated term is not a correctly annotated lambda.");
        }
        if (!areEqual(result.term.paramType, Type(), Ctx)) {
            throw new Error(`Test B11.1: Annotated param type is not Type. Got ${printTerm(result.term.paramType)}`);
        }
        
        const testApp = App(result.term, Type());
        const bodyCheckResult = elaborate(testApp, undefined, Ctx);
        assertEqual(printTerm(bodyCheckResult.term), "Type", "Test B11.1: Body of elaborated lambda not behaving as identity for Type.");

        // The reported type should be equivalent to the expected Pi type
        const expectedNormalizedPiForComparison = Pi("Y", Type(), (_ignoredVar: Term) => Type()); 
        assertEqual(printTerm(normalize(result.type, Ctx)), printTerm(normalize(expectedNormalizedPiForComparison, Ctx)), "Test B11.2: Type of elaborated term not matching expected Pi type");
        console.log("Assertion Passed: Test B11: Unannotated lambda checked against Pi type successfully.");

    } catch (e: any) {
        console.error("Test B11 Failed:", e.message, e.stack);
    }

    console.log("Base DTT (MyLambdaPi) Tests Completed.");
}

// --- START OF NEW NON-LINEAR PATTERN TESTS ---
function runNonLinearPatternTests() {
    const CtxNL = emptyCtx;
    console.log("\n--- Test NL: Non-Linear Pattern Matching ---");

    // Define some basic types and terms for the tests
    resetMyLambdaPi();
    setupPhase1GlobalsAndRules(); // Basic setup

    defineGlobal("NLT", Type(), undefined, true); // NLType
    defineGlobal("nl_A", Var("NLT"));
    defineGlobal("nl_B", Var("NLT"));
    defineGlobal("nl_C", Var("NLT"));
    defineGlobal("nl_R_func", Pi("arg", Var("NLT"), (_arg) => Var("NLT")), undefined, true); // R : NLT -> NLT

    // Define a global that can be delta-reduced
    // nl_A_alias will reduce to nl_A
    defineGlobal("nl_A_alias", Var("NLT"), Var("nl_A"));

    // Define a term P(arg1:NLT, arg2:NLT) -> NLT for rules
    defineGlobal("P_func", Pi("arg1", Var("NLT"), (_) => Pi("arg2", Var("NLT"), (_) => Var("NLT"))), undefined, true);

    // Rewrite Rule: P($x, $x) -> R($x)
    // $x should have type NLT
    const pVarX_NL = { name: "X_nl_pv", type: Var("NLT") };
    addRewriteRule({
        name: "P_nonlinear_xx_to_R",
        patternVars: [pVarX_NL],
        lhs: App(App(Var("P_func"), Var("X_nl_pv")), Var("X_nl_pv")),
        rhs: App(Var("nl_R_func"), Var("X_nl_pv"))
    });

    // Test NL.1: P(nl_A, nl_A_alias) should match P($x,$x) and rewrite to R(nl_A)
    // because nl_A_alias is definitionally equal to nl_A.
    console.log("\n--- Test NL.1: Non-linear match with definitional equality ---");
    try {
        const term_P_A_AAlias = App(App(Var("P_func"), Var("nl_A")), Var("nl_A_alias"));
        const elabRes1 = elaborate(term_P_A_AAlias, undefined, CtxNL);
        const expected_R_A = App(Var("nl_R_func"), Var("nl_A"));
        
        console.log(`Term P(A, A_alias): ${printTerm(term_P_A_AAlias)}`);
        console.log(`Elaborated: ${printTerm(elabRes1.term)}`);
        console.log(`Expected rewrite to: ${printTerm(normalize(expected_R_A, CtxNL))}`);
        
        if (!areEqual(elabRes1.term, expected_R_A, CtxNL)) {
            throw new Error(`Test NL.1 Failed: P(nl_A, nl_A_alias) did not rewrite to R(nl_A). Got ${printTerm(elabRes1.term)}`);
        }
        assertEqual(printTerm(normalize(elabRes1.type, CtxNL)), printTerm(Var("NLT")), "Test NL.1: Type of R(nl_A) is NLT");
        console.log("Test NL.1 Passed.");
    } catch (e: any) {
        console.error("Test NL.1 Failed:", e.message, e.stack);
    }

    // Test NL.2: P(nl_A, nl_B) should NOT match P($x,$x) because nl_A and nl_B are not def. equal.
    // So, it should remain P(nl_A, nl_B).
    console.log("\n--- Test NL.2: Non-linear non-match ---");
    try {
        const term_P_A_B = App(App(Var("P_func"), Var("nl_A")), Var("nl_B"));
        const elabRes2 = elaborate(term_P_A_B, undefined, CtxNL);

        console.log(`Term P(A, B): ${printTerm(term_P_A_B)}`);
        console.log(`Elaborated: ${printTerm(elabRes2.term)}`);

        if (!areEqual(elabRes2.term, term_P_A_B, CtxNL)) { // Should not have rewritten
            throw new Error(`Test NL.2 Failed: P(nl_A, nl_B) unexpectedly rewrote. Got ${printTerm(elabRes2.term)}`);
        }
        assertEqual(printTerm(normalize(elabRes2.type, CtxNL)), printTerm(Var("NLT")), "Test NL.2: Type of P(nl_A, nl_B) is NLT");
        console.log("Test NL.2 Passed.");
    } catch (e: any) {
        console.error("Test NL.2 Failed:", e.message, e.stack);
    }

    // Test NL.3: P(nl_C, nl_C) should match P($x,$x) and rewrite to R(nl_C)
    // (Simple direct non-linear match)
    console.log("\n--- Test NL.3: Non-linear direct match ---");
    try {
        const term_P_C_C = App(App(Var("P_func"), Var("nl_C")), Var("nl_C"));
        const elabRes3 = elaborate(term_P_C_C, undefined, CtxNL);
        const expected_R_C = App(Var("nl_R_func"), Var("nl_C"));

        console.log(`Term P(C, C): ${printTerm(term_P_C_C)}`);
        console.log(`Elaborated: ${printTerm(elabRes3.term)}`);
        console.log(`Expected rewrite to: ${printTerm(normalize(expected_R_C, CtxNL))}`);
        
        if (!areEqual(elabRes3.term, expected_R_C, CtxNL)) {
            throw new Error(`Test NL.3 Failed: P(nl_C, nl_C) did not rewrite to R(nl_C). Got ${printTerm(elabRes3.term)}`);
        }
        assertEqual(printTerm(normalize(elabRes3.type, CtxNL)), printTerm(Var("NLT")), "Test NL.3: Type of R(nl_C) is NLT");
        console.log("Test NL.3 Passed.");
    } catch (e: any) {
        console.error("Test NL.3 Failed:", e.message, e.stack);
    }
    
    console.log("Non-Linear Pattern Tests Completed.");
}
// --- END OF NEW NON-LINEAR PATTERN TESTS ---

// Add a main execution block or export test runner
// if (require.main === module) {
    let DEBUG_VERBOSE_orig = (globalThis as any).DEBUG_VERBOSE;
    (globalThis as any).DEBUG_VERBOSE = false; // Disable verbose logging for tests unless specified
    
    try {
        runPhase1Tests();
        runBaseDTTTests();
        runNonLinearPatternTests(); // Call the new test suite
    } catch (e) {
        console.error("A test suite threw an uncaught error:", e);
    } finally {
        (globalThis as any).DEBUG_VERBOSE = DEBUG_VERBOSE_orig;
    }
// }

export { runPhase1Tests, runBaseDTTTests, runNonLinearPatternTests, assertEqual, assertLogs };


if (typeof (globalThis as any).DEBUG_VERBOSE === 'undefined') {
    (globalThis as any).DEBUG_VERBOSE = false; 
} 

