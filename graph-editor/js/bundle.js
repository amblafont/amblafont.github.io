"use strict";
var Bundle = (() => {
  var __defProp = Object.defineProperty;
  var __getOwnPropDesc = Object.getOwnPropertyDescriptor;
  var __getOwnPropNames = Object.getOwnPropertyNames;
  var __hasOwnProp = Object.prototype.hasOwnProperty;
  var __export = (target, all) => {
    for (var name in all)
      __defProp(target, name, { get: all[name], enumerable: true });
  };
  var __copyProps = (to, from, except, desc) => {
    if (from && typeof from === "object" || typeof from === "function") {
      for (let key of __getOwnPropNames(from))
        if (!__hasOwnProp.call(to, key) && key !== except)
          __defProp(to, key, { get: () => from[key], enumerable: !(desc = __getOwnPropDesc(from, key)) || desc.enumerable });
    }
    return to;
  };
  var __toCommonJS = (mod) => __copyProps(__defProp({}, "__esModule", { value: true }), mod);

  // ts/bundle.ts
  var bundle_exports = {};
  __export(bundle_exports, {
    broadcastDataOnSocket: () => broadcastDataOnSocket,
    checkWatchedFile: () => checkWatchedFile,
    defaultConfig: () => defaultConfig,
    defaultsExt: () => defaultsExt,
    getTextFromFilepath: () => getTextFromFilepath,
    handleServerToClientMsg: () => handleServerToClientMsg,
    requestSnapshot: () => requestSnapshot,
    resetExpectedId: () => resetExpectedId,
    watchSaveDiagram: () => watchSaveDiagram
  });

  // ts/watcher.ts
  var defaultConfig = {
    magic: "% YADE DIAGRAM",
    externalOutput: false,
    exportFormat: "tex",
    baseDir: ".",
    prefixes: [],
    suffixes: [],
    includeCmd: "\\input{@}",
    preambleFile: ""
  };
  var defaultsExt = {
    "tex": {
      prefix: "% GENERATED LATEX",
      suffix: "% END OF GENERATED LATEX",
      includeCmd: "\\input{@}"
    },
    "lyx": {
      prefix: "\\end_layout\\n\\end_inset\\n\\begin_inset Preview \\n\\begin_layout Standard\\n\\begin_inset CommandInset include\\nLatexCommand input\\npreview true",
      suffix: "\\end_inset\\n\\end_layout\\n\\end_inset\\n\\begin_inset Note Note\\nstatus open\\n\\begin_layout Plain Layout",
      includeCmd: 'filename "@"',
      externalOutput: true
    },
    "md": {
      prefix: "-->\\n<!-- GENERATED SVG -->",
      suffix: "<!-- END OF GENERATED SVG -->\\n<!-- ",
      exportFormat: "svg"
    },
    "v": {
      prefix: "*)\\n(* GENERATED COQ SCRIPT *)",
      suffix: "(* END OF GENERATED COQ SCRIPT *)\\n(* ",
      exportFormat: "coq"
    }
  };
  function hasProperty(obj, key) {
    return key in obj;
  }
  for (let key in defaultsExt) {
    if (!hasProperty(defaultsExt, key))
      continue;
    const entry = defaultsExt[key];
    entry["prefixes"] = entry.prefix.split("\\n");
    entry["suffixes"] = entry.suffix.split("\\n");
    delete entry.prefix;
    delete entry.suffix;
  }
  function joinPath(...parts) {
    return parts.join("/");
  }
  function pathBasename(p) {
    let lastDot = p.lastIndexOf(".");
    let startIdx = 0;
    let endIdx = lastDot === -1 ? p.length : lastDot;
    return p.substring(startIdx, endIdx);
  }
  function outputFileName(config, content) {
    return joinPath(config.baseDir, pathBasename(content) + "." + config.exportFormat);
  }
  async function getFilehandleFromPath(d, filePath, options) {
    let parts = filePath.split("/");
    let currentHandle = d;
    while (parts.length > 1) {
      const part = parts.shift();
      if (part == ".")
        continue;
      currentHandle = await currentHandle.getDirectoryHandle(part);
    }
    return currentHandle.getFileHandle(parts[0], options);
  }
  async function checkFileExistsFromPath(d, filePath) {
    try {
      await getFilehandleFromPath(d, filePath);
      return true;
    } catch (e) {
      return false;
    }
  }
  async function getTextFromFilepath(d, filePath) {
    let filehandle = await getFilehandleFromPath(d, filePath);
    let file = await filehandle.getFile();
    return file.text();
  }
  function getLinesFromFilepath(d, filePath) {
    return getTextFromFilepath(d, filePath).then((text) => text.split("\n"));
  }
  function readLine(s) {
    let line = s.shift();
    if (line === void 0) {
      return false;
    }
    return line;
  }
  function escapeStringRegexp(s) {
    return s.replace(/[/\-\\^$*+?.()|[\]{}]/g, "\\$&");
  }
  function parseMagic(magic, line) {
    let magicRe = new RegExp(escapeStringRegexp(magic.trim()) + "(.*)$");
    let search = magicRe.exec(line.trim());
    if (search !== null) {
      let indent = line.search(/\S|$/);
      return {
        content: search[1].trim(),
        indent: line.substring(0, indent)
      };
    } else {
      return { content: null, indent: "" };
    }
  }
  function parsePrefix(line, remainder_arg) {
    let remainder = [...remainder_arg];
    if (remainder.length == 0) {
      return [];
    }
    let linestrip = line.trim();
    if (linestrip === "") {
      return remainder;
    }
    let head = remainder.shift().trim();
    if (head === "") {
      parsePrefix(linestrip, remainder);
    }
    if (linestrip === head) {
      return remainder;
    } else {
      return null;
    }
  }
  function contentIsFile(content) {
    return content.trim() != "" && content.trim().charAt(0) != "{";
  }
  function contentToFileName(config, content) {
    return joinPath(config.baseDir, content);
  }
  async function fsWriteFile(d, filename, content) {
    let fileHandle = await getFilehandleFromPath(d, filename, { create: true });
    let writer = await fileHandle.createWritable();
    await writer.write(content);
    await writer.close();
  }
  function writeLine(fd, line) {
    if (line !== false)
      fd.push(line + "\n");
  }
  function writeLines(fd, lines, indent) {
    for (let line of lines) {
      writeLine(fd, indent + line);
    }
  }
  async function writeContent(config, d, newcontent, output, index) {
    let fd = [];
    const file_lines = await getLinesFromFilepath(d, config.watchedFile);
    let line = false;
    let content = null;
    let indent = "";
    for (let i = 0; i < index; i++) {
      writeLine(fd, line);
      content = null;
      line = false;
      while (content === null) {
        writeLine(fd, line);
        line = readLine(file_lines);
        if (line === false)
          break;
        let magic = parseMagic(config.magic, line);
        content = magic.content;
        indent = magic.indent;
      }
    }
    if (content === null) {
      console.log("error");
      throw new Error("error");
      return;
    }
    let isFile = contentIsFile(content);
    if (isFile)
      writeLine(fd, line);
    else
      writeLine(fd, indent + config.magic + " " + newcontent);
    writeLines(fd, config.prefixes, indent);
    if (!config.externalOutput || !isFile)
      writeLines(fd, output.split("\n"), indent);
    else
      writeLine(fd, indent + config.includeCmd.replace("@", outputFileName(config, content)));
    writeLines(fd, config.suffixes, indent);
    while (line !== false) {
      line = readLine(file_lines);
      if (line === false) {
        break;
      }
      writeLine(fd, line);
    }
    return fsWriteFile(d, config.watchedFile, fd.join(""));
  }
  async function watchSaveDiagram(config, handleConfig, d, newcontent_json, exports) {
    let newcontent = JSON.stringify(newcontent_json);
    let generatedOutput = exports[config.exportFormat];
    if (handleConfig.diagFile !== null) {
      let wfile = contentToFileName(config, handleConfig.diagFile);
      console.log("writing to the file " + wfile);
      await fsWriteFile(d, wfile, newcontent);
      if (config.externalOutput) {
        let outputFile = outputFileName(config, handleConfig.diagFile);
        await fsWriteFile(d, outputFile, generatedOutput);
      }
    }
    if (!handleConfig.onlyExternalFile)
      await writeContent(config, d, newcontent, generatedOutput, handleConfig.index);
  }
  async function getContent(d, config, diagFile) {
    let content = "";
    let rfile = contentToFileName(config, diagFile);
    try {
      let fileHandle = await getFilehandleFromPath(d, rfile);
      let file = await fileHandle.getFile();
      content = await file.text();
    } catch (e) {
      console.log("Error when accessing " + rfile);
      console.log(e);
    }
    return content;
  }
  async function checkWatchedFile(config, d) {
    let file_lines;
    try {
      file_lines = await getLinesFromFilepath(d, config.watchedFile);
    } catch (e) {
      alert("Unable to read " + config.watchedFile);
      console.log(e);
      return void 0;
    }
    let remainder = [];
    let index = 0;
    let line = "";
    let content = null;
    while (line !== false && remainder !== null && remainder.length == 0) {
      index++;
      content = null;
      while (content === null) {
        line = readLine(file_lines);
        if (line === false)
          break;
        content = parseMagic(config.magic, line).content;
      }
      if (line === false)
        break;
      console.log("Graph found");
      if (content !== null && config.exportFormat && contentIsFile(content)) {
        let diagFile2 = content;
        let outputFile = outputFileName(config, diagFile2);
        let checkExist = await checkFileExistsFromPath(d, outputFile);
        let rfile = contentToFileName(config, diagFile2);
        let checkExistRfile = await checkFileExistsFromPath(d, rfile);
        if (checkExistRfile && !checkExist) {
          let data = await getContent(d, config, diagFile2);
          return {
            diagFile: diagFile2,
            index,
            content: data,
            onlyExternalFile: true
          };
        }
        if (!checkExistRfile)
          console.log("File " + rfile + " doesn't exist.");
      }
      remainder = config.prefixes;
      while (remainder !== null && remainder.length > 0) {
        line = readLine(file_lines);
        if (line === false)
          break;
        remainder = parsePrefix(line, remainder);
      }
    }
    if (!((remainder === null || remainder.length > 0) && content !== null)) {
      return false;
    }
    console.log("do something with " + content);
    let diagFile = null;
    if (contentIsFile(content)) {
      diagFile = content;
      content = await getContent(d, config, content);
    }
    let handleConfig = { content, diagFile, index, onlyExternalFile: false };
    return handleConfig;
  }

  // ts/client.ts
  var expectedIdFromServer = 0;
  function resetExpectedId() {
    expectedIdFromServer = 0;
  }
  function requestSnapshot(ws) {
    let msg = null;
    sendDataOnSocket(ws, {
      snapshot: false,
      break: false,
      history: false,
      broadcast: false,
      msg
    });
  }
  function handleServerToClientMsg(ws, snapshotRequest, normalRequest, data) {
    let msg = JSON.parse(data);
    switch (msg.type) {
      case "diffs":
        handleServerToClientDiffs(ws, normalRequest, msg.data);
        break;
      case "snapshotRequest":
        snapshotRequest(null);
        break;
    }
  }
  function handleServerToClientDiffs(ws, normalRequest, data) {
    let diffs = [];
    for (let i = 0; i < data.length; i++) {
      let diff = data[i];
      if (diff.id > expectedIdFromServer && !diff.snapshot) {
        requestSnapshot(ws);
        return [];
      }
      expectedIdFromServer = diff.id + 1;
      diffs.push(diff);
    }
    normalRequest(diffs);
  }
  function sendDiffOnSocket(ws, d) {
    console.log("sending data on websocket");
    console.log(d);
    ws.send(JSON.stringify(d));
  }
  function sendDataOnSocket(ws, data) {
    let moreData = Object.assign(data, { "expectedId": expectedIdFromServer });
    sendDiffOnSocket(ws, moreData);
  }
  function broadcastDataOnSocket(ws, data) {
    sendDataOnSocket(ws, { ...data, broadcast: true });
  }
  return __toCommonJS(bundle_exports);
})();
