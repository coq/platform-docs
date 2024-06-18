// author: Colin Vidal

function extractSession() {
    let buffer = ""
    const codeBlocks = document.getElementsByClassName("CodeMirror-code")
    for (const codeBlock of codeBlocks) {
        const lineContainers = codeBlock.getElementsByClassName("CodeMirror-line")
        for (const lineContainer of lineContainers) {
            const line = lineContainer.firstChild
            if (line) {
                    // UTF16 representation of a non printable character breaking coq lexer
                    // in two whitespace-only lines between the two contraposé theorems
                    buffer += line.innerText.replace(/\u200b/g, "")
            } else {
                alert("possible missing data")
            }
            buffer += "\n"
        }
        buffer += "\n\n"
    }
    
    // Coqjs automatically makes ligatures -- let's reverse this to avoid upcoming lexer issues.
    return buffer.replace(/ℙ/g, "Prop")
                 .replace(/∀/g, "forall")
                 .replace(/→/g, "->")
                 .replace(/↔/g, "<->")
                 .replace(/∧/g, "/\\")
                 .replace(/∨/g, "\\/")
}
    
    
function downloadSession(fileName) {
    let el = document.createElement("a");
    el.setAttribute("href", "data:text/plain;charset=utf-8," + encodeURIComponent(extractSession()));
    el.setAttribute("download", fileName);
    el.style.display = "none";
    document.body.appendChild(el);
    el.click();
    document.body.removeChild(el);
}

function setup() {
    let el = document.createElement("button");
    el.onclick = () => downloadSession("session.v")
    el.innerHTML = "download session"
    el.style = "position: absolute; right: 40px; top: 5px; z-index:999; width: 200px;"
    document.body.appendChild(el)
}

setup()
