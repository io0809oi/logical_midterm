/* Stable problem IDs keep saved proofs attached when the list is reordered. */
(function(root){
'use strict';
const legacyIds=["h4-e1-1", "h4-e1-2", "h4-e2-1", "h4-e2-2", "h4-s1", "h4-s2", "h4-s3", "h4-s4", "h4-s5", "h4-s6", "h4-extra1", "h4-extra2", "h4-extra3", "h4-true1", "h4-true2", "h4-false1", "h4-false2", "h4-incon1", "h4-incon2", "h5-proof-dn", "h5-proof-mt", "h5-proof-ca", "h5-proof-cp", "h5-proof-w", "h5-proof-ac", "h5-proof-cr", "h5-proof-ar", "h5-proof-dr1", "h5-proof-dr2", "h5-proof-dm1", "h5-proof-dm2", "h5-proof-c1", "h5-proof-c2", "h5-e1", "h5-e2", "h5-e3", "h5-e4", "h5-t1", "h5-t2", "h5-t3", "h5-t4", "h5-lang1", "h5-lang2", "h5-lang3", "own-1", "own-2", "own-3", "own-4", "own-5", "own-6", "own-7", "own-8", "own-9", "own-10", "own-11", "own-12"];
function normalize(saved,problems,legacy=false){
 saved=saved&&typeof saved==='object'?saved:{};
 const ids=new Set(problems.map(p=>p.id)),drafts={};
 for(const [key,value] of Object.entries(saved.drafts||{})){
  const id=legacy?legacyIds[Number(key)]:key;
  if(ids.has(id)&&value&&value.state&&Array.isArray(value.state.lines)&&Array.isArray(value.history))drafts[id]=value;
 }
 const solved=(Array.isArray(saved.solved)?saved.solved:[]).filter(id=>ids.has(id));
 const requested=legacy?legacyIds[saved.current]:saved.currentId;
 return {drafts,solved,currentId:ids.has(requested)?requested:problems[0]?.id};
}
const api={normalize};
if(typeof module!=='undefined')module.exports=api;else root.LogicProgress=api;
})(typeof globalThis!=='undefined'?globalThis:this);
