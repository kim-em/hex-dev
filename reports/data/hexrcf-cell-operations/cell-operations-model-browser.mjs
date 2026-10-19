import fs from 'node:fs';
import {spawn} from 'node:child_process';
const root=process.argv[2];
if(!root) throw new Error('Pass the scratch render directory');
const profile=root+'/cell-operations-model-profile';
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
 await call('Page.navigate',{url:'file://'+root+'/cell-operations-html/html-single/index.html'});
 await load;
 const evaluate=async expression=>{const r=await call('Runtime.evaluate',{expression,returnByValue:true});if(r.exceptionDetails)throw new Error(JSON.stringify(r.exceptionDetails));return r.result.value;};
 const metadata=[];
 for(const [label,width] of [['desktop',1440],['narrow',390]]) {
  await call('Emulation.setDeviceMetricsOverride',{width,height:1000,deviceScaleFactor:1,mobile:false});
  for(const [kind,phrase] of [['api-start',"The complete literal checker can use checked cached arithmetic"],['api-end',"The complete literal checker can use checked cached arithmetic"],['scope','Original guard preflight, radical identities'],['model','For a closed retained base/root context']] ) {
   const exact=await evaluate(`(() => {const p=Array.from(document.querySelectorAll('p')).find(e=>e.textContent.replace(/\\s+/g,' ').includes(${JSON.stringify(phrase)}));if(!p)throw new Error('missing paragraph '+${JSON.stringify(phrase)});const target=['api-start','api-end'].includes(${JSON.stringify(kind)})?(()=>{let t=p.nextElementSibling;while(t&&!t.matches('.hl.lean.block, pre, div:has(code)'))t=t.nextElementSibling;if(!t)throw new Error('missing discovery code');return t;})():p;if(['api-start','api-end'].includes(${JSON.stringify(kind)})&&!target.matches('.hl.lean.block, pre, div:has(code)'))throw new Error('target is not a Lean code block');target.scrollIntoView({block:${JSON.stringify(kind==='api-start'?'start':kind==='api-end'?'end':'center')}});if(${JSON.stringify(kind)}==='api-start')scrollBy(0,-80);return {anchorText:p.textContent,targetTop:target.getBoundingClientRect().top,targetBottom:target.getBoundingClientRect().bottom,viewport:innerWidth,scrollY,paragraphWidth:p.getBoundingClientRect().width,scrollWidth:p.scrollWidth,targetTag:target.tagName,targetWidth:target.getBoundingClientRect().width,targetScrollWidth:target.scrollWidth,descendantOverflow:Math.max(0,...[target,...target.querySelectorAll('*')].map(e=>e.scrollWidth-e.clientWidth))};})()`);
   if(!exact)throw new Error('missing visual target '+kind);
   const overflows = exact.targetScrollWidth > exact.targetWidth + 1 || exact.descendantOverflow > 1;
   await evaluate('new Promise(resolve=>requestAnimationFrame(()=>requestAnimationFrame(resolve)))');
   const shot=await call('Page.captureScreenshot',{format:'png'});
   fs.writeFileSync(root+'/'+'cell-operations-model-'+label+'-'+kind+'.png',Buffer.from(shot.data,'base64'));
   metadata.push({label,kind,...exact});
   if(overflows) {fs.writeFileSync(root+'/cell-operations-model-overflow.json',JSON.stringify({label,kind,...exact},null,2));throw new Error('changed content overflows: '+kind);}
  }
 }
 fs.writeFileSync(root+'/cell-operations-model-inspection.json',JSON.stringify(metadata,null,2));
 process.stdout.write('Saved cell-operations-model desktop/narrow screenshots\n');
} finally {if(socket)socket.close();chrome.kill('SIGTERM');}
