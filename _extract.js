const fs=require('fs');
const h=fs.readFileSync('index.html','utf8');
const i=h.indexOf('<script>');
const j=h.lastIndexOf('</script>');
fs.writeFileSync('_check.js',h.slice(i+8,j));
console.log('script lines:',h.slice(i+8,j).split('\n').length);
