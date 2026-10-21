'use strict';
const assert=require('node:assert/strict'),T=require('../dist/traditional-logic.js');
const expected=[true,true,false,true,false,true,false,true,true,true];
// Independent finite-domain interpretation of categorical statements.
function truth([k,s,p],objects,exist){const ss=objects.filter(o=>o[s]),both=ss.filter(o=>o[p]);return k==='A'?ss.every(o=>o[p])&&(!exist||ss.length>0):k==='E'?both.length===0&&(!exist||ss.length>0):k==='I'?both.length>0:ss.some(o=>!o[p]);}
function objectModels(p,mode){const all=[];for(let mask=1;mask<256;mask++){const obs=[];for(let cell=0;cell<8;cell++)if(mask&(2**cell))obs.push([0,1,2].map(b=>!!(cell&(2**b))));if(p.singleton!==null&&obs.filter(o=>o[p.singleton]).length!==1)continue;if(p.premises.every(f=>truth(f,obs,mode==='aristotle')))all.push({mask,valid:truth(p.goal,obs,mode==='aristotle')});}return all;}
let cases=0;
for(const p of T.problems)for(const mode of p.modes){cases++;const ms=objectModels(p,mode),d=T.canonical(p,mode),cs=T.countermodels(p,mode);assert.deepEqual(T.models(p,mode),ms.map(x=>x.mask));assert.deepEqual(cs,ms.filter(x=>!x.valid).map(x=>x.mask));assert.equal(cs.length===0,p.number===7&&mode==='aristotle'?true:expected[p.number-1]);T.checkDiagram(p,mode,d);assert.equal(T.check(p,mode,d,cs.length?'invalid':'valid',cs[0],{type:'A',direction:'wise-philosopher'}),cs.length?'invalid':'valid');assert.throws(()=>T.check(p,mode,d,cs.length?'valid':'invalid',cs[0],{type:'A',direction:'wise-philosopher'}));}
assert.equal(cases,11);
const p=T.problems[2],d=T.canonical(p);assert.deepEqual(d.groups,[[6,7]]);assert.throws(()=>T.checkDiagram(p,'boole',{shaded:d.shaded,groups:[[7]]}));assert.throws(()=>T.checkDiagram(p,'boole',{shaded:d.shaded,groups:[[6],[7]]}));assert.throws(()=>T.checkDiagram(p,'boole',{shaded:[],groups:[]}));assert.throws(()=>T.check(p,'boole',d,'invalid',0));
const boole=T.canonical(T.problems[6]);assert.equal(boole.groups.length,0);assert.throws(()=>T.checkDiagram(T.problems[6],'boole',{...boole,groups:[[7]]}));assert.throws(()=>T.checkDiagram(T.problems[6],'aristotle',boole));
const q=T.problems[8];assert.throws(()=>T.check(q,'boole',T.canonical(q),'valid',0,{type:'A',direction:'philosopher-wise'}));assert.throws(()=>T.check(q,'boole',T.canonical(q),'valid',0,{type:'I',direction:'wise-philosopher'}));
assert.ok(T.models(T.problems[9]).every(m=>T.regions.filter(r=>T.occupied(m,r)&&T.inside(r,0)).length===1));
console.log('PASS traditional logic: 10 exercises / 11 verdicts, independent finite models, Venn equivalence, existence, translation, counterexamples.');
