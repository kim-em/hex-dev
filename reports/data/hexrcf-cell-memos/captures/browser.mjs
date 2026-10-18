import fs from 'node:fs';
import {spawn} from 'node:child_process';
const root=process.argv[2];
if(!root) throw new Error('Pass the scratch render directory');
const profile=root+'/cell-memo-profile';
fs.mkdirSync(profile,{recursive:true});
fs.rmSync(profile+'/DevToolsActivePort',{force:true});
const chrome=spawn(process.env.CHROME_BIN || '/home/kim/.cache/ms-playwright/chromium-1243/chrome-linux64/chrome',[
 '--headless=new','--no-sandbox','--disable-gpu','--allow-file-access-from-files',
 '--remote-debugging-port=0','--remote-allow-origins=*','--user-data-dir='+profile,'about:blank'],
 {env:{...process.env,LD_LIBRARY_PATH:fs.readFileSync(root+'/browser-lib-paths.txt','utf8').trim()},stdio:'ignore'});
let socket;
try {
 const portFile=profile+'/DevToolsActivePort';
 for(let i=0;!fs.existsSync(portFile);i++) {
  if(i>200||chrome.exitCode!==null) throw new Error('Chrome did not expose CDP');
  await new Promise(r=>setTimeout(r,100));
 }
 const port=fs.readFileSync(portFile,'utf8').split('\n')[0];
 const tabs=await (await fetch('http://127.0.0.1:'+port+'/json')).json();
 socket=new WebSocket(tabs.find(t=>t.type==='page').webSocketDebuggerUrl);
 await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j});
 let sequence=0;const pending=new Map();let loaded;
 socket.onmessage=e=>{
  const msg=JSON.parse(e.data);
  if(msg.id){const p=pending.get(msg.id);pending.delete(msg.id);msg.error?p.reject(msg.error):p.resolve(msg.result);}
  if(msg.method==='Page.loadEventFired'&&loaded){loaded();loaded=undefined;}
 };
 const call=(method,params={})=>new Promise((resolve,reject)=>{const id=++sequence;pending.set(id,{resolve,reject});socket.send(JSON.stringify({id,method,params}));});
 await call('Page.enable');
 const load=new Promise(r=>loaded=r);
 await call('Page.navigate',{url:'file:///home/kim/.codex/tasks/hex-10358/scalar-review-render/cell-memo-review-html/html-single/index.html'});
 await load;
 const evaluate=async expression=>{const r=await call('Runtime.evaluate',{expression,returnByValue:true});if(r.exceptionDetails)throw new Error(JSON.stringify(r.exceptionDetails));return r.result.value;};
 const metadata=[]; const sectionMetadata=[];
 for(const [label,width] of [['desktop',1440],['narrow',390]]) {
  await call('Emulation.setDeviceMetricsOverride',{width,height:width===390?1800:1000,deviceScaleFactor:1,mobile:false});
  for(const [kind,phrase] of [["memo", "Within this request, row quotation parses each literal sign packet"], ["measurements", "A separate rational quadratic packet checks two root sections"], ["audit", "A fresh importing audit checks 1,246 theorem bodies"], ["source", "The algebraic source regression independently reads the complete frozen packet"], ["sourcecode", "The algebraic source regression independently reads the complete frozen packet"]] ) {
   const exact=await evaluate(`(() => {const p=Array.from(document.querySelectorAll('p')).find(e=>e.textContent.replace(/\\s+/g,' ').includes(${JSON.stringify(phrase)}));if(!p)throw new Error('missing paragraph');const target=['sourcecode'].includes(${JSON.stringify(kind)})?p.nextElementSibling:p;if(['sourcecode'].includes(${JSON.stringify(kind)})&&!target.matches('.hl.lean.block, pre, div:has(code)'))throw new Error('target is not a Lean code block');target.scrollIntoView({block:${JSON.stringify('center')}});return {text:p.textContent,viewport:innerWidth,scrollY,paragraphWidth:p.getBoundingClientRect().width,scrollWidth:p.scrollWidth,targetTag:target.tagName,targetWidth:target.getBoundingClientRect().width,targetScrollWidth:target.scrollWidth,descendantOverflow:Math.max(0,...[target,...target.querySelectorAll('*')].map(e=>e.scrollWidth-e.clientWidth)),overflowElements:[target,...target.querySelectorAll('*')].filter(e=>e.scrollWidth-e.clientWidth>1).map(e=>({tag:e.tagName,classes:e.className,width:e.clientWidth,scroll:e.scrollWidth,text:e.textContent.slice(0,100)})).slice(0,8)};})()`);
   if(!exact)throw new Error('missing visual target '+kind);
   await evaluate('new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))');
   const shot=await call('Page.captureScreenshot',{format:'png'});
   fs.writeFileSync(root+'/'+'cell-memo-final-'+label+'-'+kind+'.png',Buffer.from(shot.data,'base64'));
   metadata.push({label,kind,...exact});
  }
  sectionMetadata.push(await evaluate(`(() => {
    const headings=Array.from(document.querySelectorAll('h1,h2,h3,h4,h5,h6'));
    const heading=headings.find(e=>e.textContent.includes('Quoting a supplied root replay'));
    if(!heading)throw new Error('missing quotation heading');
    const following=headings.find(e=>e!==heading && Number(e.tagName[1])<=Number(heading.tagName[1]) && (heading.compareDocumentPosition(e)&4));
    if(!following)throw new Error('missing following section');
    const targets=Array.from(document.querySelectorAll('p,.hl.lean.block')).filter(e=>(heading.compareDocumentPosition(e)&4) && (e.compareDocumentPosition(following)&4));
    if(targets.length<8)throw new Error('incomplete quotation section');
    return {label:${JSON.stringify(label)},width:innerWidth,targets:targets.map(e=>({tag:e.tagName,text:e.textContent.slice(0,160),overflow:Math.max(0,...[e,...e.querySelectorAll('*')].map(n=>n.scrollWidth-n.clientWidth))}))};
  })()`));
 }
 fs.writeFileSync(root+'/cell-memo-final-section-overflow.json',JSON.stringify(sectionMetadata,null,2));
 fs.writeFileSync(root+'/cell-memo-final-inspection.json',JSON.stringify(metadata,null,2));
 if(metadata.some(e=>e.targetScrollWidth>e.targetWidth+1 || e.descendantOverflow>1)) throw new Error('Changed content overflows; retained captures and metrics identify the affected block.');
 process.stdout.write('Saved cell quotation desktop/narrow screenshots\n');
} finally {if(socket)socket.close();chrome.kill('SIGTERM');}
