// import {Data, ServerToClientDiffs, ClientToServerDiff, ServerToClientDiff, ServerToClientMsg} from "./interface.js";
var __assign = (this && this.__assign) || function () {
    __assign = Object.assign || function(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p))
                t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};
var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};
var __generator = (this && this.__generator) || function (thisArg, body) {
    var _ = { label: 0, sent: function() { if (t[0] & 1) throw t[1]; return t[1]; }, trys: [], ops: [] }, f, y, t, g;
    return g = { next: verb(0), "throw": verb(1), "return": verb(2) }, typeof Symbol === "function" && (g[Symbol.iterator] = function() { return this; }), g;
    function verb(n) { return function (v) { return step([n, v]); }; }
    function step(op) {
        if (f) throw new TypeError("Generator is already executing.");
        while (g && (g = 0, op[0] && (_ = 0)), _) try {
            if (f = 1, y && (t = op[0] & 2 ? y["return"] : op[0] ? y["throw"] || ((t = y["return"]) && t.call(y), 0) : y.next) && !(t = t.call(y, op[1])).done) return t;
            if (y = 0, t) op = [op[0] & 2, t.value];
            switch (op[0]) {
                case 0: case 1: t = op; break;
                case 4: _.label++; return { value: op[1], done: false };
                case 5: _.label++; y = op[1]; op = [0]; continue;
                case 7: op = _.ops.pop(); _.trys.pop(); continue;
                default:
                    if (!(t = _.trys, t = t.length > 0 && t[t.length - 1]) && (op[0] === 6 || op[0] === 2)) { _ = 0; continue; }
                    if (op[0] === 3 && (!t || (op[1] > t[0] && op[1] < t[3]))) { _.label = op[1]; break; }
                    if (op[0] === 6 && _.label < t[1]) { _.label = t[1]; t = op; break; }
                    if (t && _.label < t[2]) { _.label = t[2]; _.ops.push(op); break; }
                    if (t[2]) _.ops.pop();
                    _.trys.pop(); continue;
            }
            op = body.call(thisArg, _);
        } catch (e) { op = [6, e]; y = 0; } finally { f = t = 0; }
        if (op[0] & 5) throw op[1]; return { value: op[0] ? op[1] : void 0, done: true };
    }
};
var __spreadArray = (this && this.__spreadArray) || function (to, from, pack) {
    if (pack || arguments.length === 2) for (var i = 0, l = from.length, ar; i < l; i++) {
        if (ar || !(i in from)) {
            if (!ar) ar = Array.prototype.slice.call(from, 0, i);
            ar[i] = from[i];
        }
    }
    return to.concat(ar || Array.prototype.slice.call(from));
};
// some defaults
var defaultConfig = { magic: "% YADE DIAGRAM",
    externalOutput: false,
    exportFormat: "tex",
    baseDir: ".",
    prefixes: [],
    suffixes: [],
    includeCmd: "\\input{@}",
    preambleFile: ""
};
//
var defaultsExt = { "tex": { prefix: "% GENERATED LATEX",
        suffix: "% END OF GENERATED LATEX",
        includeCmd: "\\input{@}"
    },
    "lyx": { prefix: "\\end_layout\\n\\end_inset\\n\\begin_inset Preview \\n\\begin_layout Standard\\n\\begin_inset CommandInset include\\nLatexCommand input\\npreview true",
        suffix: "\\end_inset\\n\\end_layout\\n\\end_inset\\n\\begin_inset Note Note\\nstatus open\\n\\begin_layout Plain Layout",
        includeCmd: "filename \"@\"",
        externalOutput: true
    },
    "md": { prefix: "-->\\n<!-- GENERATED SVG -->",
        suffix: "<!-- END OF GENERATED SVG -->\\n<!-- ",
        exportFormat: "svg"
    },
    "v": { prefix: "*)\\n(* GENERATED COQ SCRIPT *)",
        suffix: "(* END OF GENERATED COQ SCRIPT *)\\n(* ",
        exportFormat: "coq"
    } };
function hasProperty(obj, key) {
    return key in obj;
}
for (var key in defaultsExt) {
    if (!hasProperty(defaultsExt, key))
        continue;
    var entry = defaultsExt[key];
    entry["prefixes"] = entry.prefix.split('\\n');
    entry["suffixes"] = entry.suffix.split('\\n');
    // remove the key prefix from entry
    delete entry.prefix;
    delete entry.suffix;
}
function joinPath() {
    var parts = [];
    for (var _i = 0; _i < arguments.length; _i++) {
        parts[_i] = arguments[_i];
    }
    return parts.join('/');
}
function pathBasename(p) {
    // let lastSlash = p.lastIndexOf('/');
    var lastDot = p.lastIndexOf('.');
    var startIdx = 0; // lastSlash + 1;
    var endIdx = lastDot === -1 ? p.length : lastDot;
    return p.substring(startIdx, endIdx);
}
function outputFileName(config, content) {
    return joinPath(config.baseDir, pathBasename(content) + "." + config.exportFormat);
}
function getFilehandleFromPath(d, filePath, options) {
    return __awaiter(this, void 0, void 0, function () {
        var parts, currentHandle, part;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    parts = filePath.split('/');
                    currentHandle = d;
                    _a.label = 1;
                case 1:
                    if (!(parts.length > 1)) return [3 /*break*/, 3];
                    part = parts.shift();
                    if (part == ".")
                        return [3 /*break*/, 1];
                    return [4 /*yield*/, currentHandle.getDirectoryHandle(part)];
                case 2:
                    currentHandle = _a.sent();
                    return [3 /*break*/, 1];
                case 3: return [2 /*return*/, currentHandle.getFileHandle(parts[0], options)];
            }
        });
    });
}
function checkFileExistsFromPath(d, filePath) {
    return __awaiter(this, void 0, void 0, function () {
        var e_1;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    _a.trys.push([0, 2, , 3]);
                    return [4 /*yield*/, getFilehandleFromPath(d, filePath)];
                case 1:
                    _a.sent();
                    return [2 /*return*/, true];
                case 2:
                    e_1 = _a.sent();
                    return [2 /*return*/, false];
                case 3: return [2 /*return*/];
            }
        });
    });
}
function getTextFromFilepath(d, filePath) {
    return __awaiter(this, void 0, void 0, function () {
        var filehandle, file;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0: return [4 /*yield*/, getFilehandleFromPath(d, filePath)];
                case 1:
                    filehandle = _a.sent();
                    return [4 /*yield*/, filehandle.getFile()];
                case 2:
                    file = _a.sent();
                    return [2 /*return*/, file.text()];
            }
        });
    });
}
function getLinesFromFilepath(d, filePath) {
    return getTextFromFilepath(d, filePath).then(function (text) { return text.split('\n'); });
}
function readLine(s) {
    var line = s.shift();
    if (line === undefined) {
        return false;
    }
    return line;
}
function escapeStringRegexp(s) {
    return s.replace(/[/\-\\^$*+?.()|[\]{}]/g, '\\$&');
}
function parseMagic(magic, line) {
    var magicRe = new RegExp(escapeStringRegexp(magic.trim()) + "(.*)$");
    var search = magicRe.exec(line.trim());
    if (search !== null) {
        var indent = line.search(/\S|$/);
        return { content: search[1].trim(),
            indent: line.substring(0, indent) };
    }
    else {
        return { content: null, indent: "" };
    }
}
function parsePrefix(line, remainder_arg) {
    // copy the array
    var remainder = __spreadArray([], remainder_arg, true);
    if (remainder.length == 0) {
        return [];
    }
    var linestrip = line.trim();
    if (linestrip === "") {
        return remainder;
    }
    // we checked that remainder is not empty above
    var head = remainder.shift().trim();
    // reaminder is now the tail
    if (head === "") {
        parsePrefix(linestrip, remainder);
    }
    if (linestrip === head) {
        return remainder;
    }
    else {
        return null;
    }
}
function contentIsFile(content) {
    return content.trim() != "" && content.trim().charAt(0) != "{";
}
function contentToFileName(config, content) {
    return joinPath(config.baseDir, content);
}
function fsWriteFile(d, filename, content) {
    return __awaiter(this, void 0, void 0, function () {
        var fileHandle, writer;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0: return [4 /*yield*/, getFilehandleFromPath(d, filename, { create: true })];
                case 1:
                    fileHandle = _a.sent();
                    return [4 /*yield*/, fileHandle.createWritable()];
                case 2:
                    writer = _a.sent();
                    return [4 /*yield*/, writer.write(content)];
                case 3:
                    _a.sent();
                    return [4 /*yield*/, writer.close()];
                case 4:
                    _a.sent();
                    return [2 /*return*/];
            }
        });
    });
}
function writeLine(fd, line) {
    if (line !== false)
        fd.push(line + "\n");
}
function writeLines(fd, lines, indent) {
    for (var _i = 0, lines_1 = lines; _i < lines_1.length; _i++) {
        var line = lines_1[_i];
        writeLine(fd, indent + line);
    }
}
function writeContent(config, d, newcontent, output, index) {
    return __awaiter(this, void 0, void 0, function () {
        var fd, file_lines, line, content, indent, i, magic, isFile;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    fd = [];
                    return [4 /*yield*/, getLinesFromFilepath(d, config.watchedFile)];
                case 1:
                    file_lines = _a.sent();
                    line = false;
                    content = null;
                    indent = "";
                    for (i = 0; i < index; i++) {
                        writeLine(fd, line);
                        content = null;
                        line = false;
                        while (content === null) {
                            writeLine(fd, line);
                            line = readLine(file_lines);
                            if (line === false)
                                break;
                            magic = parseMagic(config.magic, line);
                            content = magic.content;
                            indent = magic.indent;
                        }
                    }
                    if (content === null) {
                        console.log("error");
                        throw new Error("error");
                        return [2 /*return*/];
                    }
                    isFile = contentIsFile(content);
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
                    // fs.copyFileSync(tmpobj.name, watchedFile);
                    // console.log("on va ecrire ceci:" + fd);
                    return [2 /*return*/, fsWriteFile(d, config.watchedFile, fd.join(""))];
            }
        });
    });
}
// save
function watchSaveDiagram(config, handleConfig, d, newcontent_json, exports) {
    return __awaiter(this, void 0, void 0, function () {
        var newcontent, generatedOutput, wfile, outputFile;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    newcontent = JSON.stringify(newcontent_json);
                    generatedOutput = exports[config.exportFormat];
                    if (!(handleConfig.diagFile !== null)) return [3 /*break*/, 3];
                    wfile = contentToFileName(config, handleConfig.diagFile);
                    console.log("writing to the file " + wfile);
                    return [4 /*yield*/, fsWriteFile(d, wfile, newcontent)];
                case 1:
                    _a.sent();
                    if (!config.externalOutput) return [3 /*break*/, 3];
                    outputFile = outputFileName(config, handleConfig.diagFile);
                    return [4 /*yield*/, fsWriteFile(d, outputFile, generatedOutput)];
                case 2:
                    _a.sent();
                    _a.label = 3;
                case 3:
                    if (!!handleConfig.onlyExternalFile) return [3 /*break*/, 5];
                    return [4 /*yield*/, writeContent(config, d, newcontent, generatedOutput, handleConfig.index)];
                case 4:
                    _a.sent();
                    _a.label = 5;
                case 5: return [2 /*return*/];
            }
        });
    });
}
function getContent(d, config, diagFile) {
    return __awaiter(this, void 0, void 0, function () {
        var content, rfile, fileHandle, file, e_2;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    content = "";
                    rfile = contentToFileName(config, diagFile);
                    _a.label = 1;
                case 1:
                    _a.trys.push([1, 5, , 6]);
                    return [4 /*yield*/, getFilehandleFromPath(d, rfile)];
                case 2:
                    fileHandle = _a.sent();
                    return [4 /*yield*/, fileHandle.getFile()];
                case 3:
                    file = _a.sent();
                    return [4 /*yield*/, file.text()];
                case 4:
                    content = _a.sent();
                    return [3 /*break*/, 6];
                case 5:
                    e_2 = _a.sent();
                    console.log("Error when accessing " + rfile);
                    console.log(e_2);
                    return [3 /*break*/, 6];
                case 6: return [2 /*return*/, content];
            }
        });
    });
}
// undefined means error
// false means no update
function checkWatchedFile(config, d) {
    return __awaiter(this, void 0, void 0, function () {
        var file_lines, e_3, remainder, index, line, content, diagFile_1, outputFile, checkExist, rfile, checkExistRfile, data, diagFile, handleConfig;
        return __generator(this, function (_a) {
            switch (_a.label) {
                case 0:
                    _a.trys.push([0, 2, , 3]);
                    return [4 /*yield*/, getLinesFromFilepath(d, config.watchedFile)];
                case 1:
                    file_lines = _a.sent();
                    return [3 /*break*/, 3];
                case 2:
                    e_3 = _a.sent();
                    alert("Unable to read " + config.watchedFile);
                    console.log(e_3);
                    return [2 /*return*/, undefined];
                case 3:
                    remainder = [];
                    index = 0;
                    line = "";
                    content = null;
                    _a.label = 4;
                case 4:
                    if (!(line !== false && remainder !== null && remainder.length == 0)) return [3 /*break*/, 10];
                    index++;
                    content = null;
                    while (content === null) {
                        line = readLine(file_lines);
                        if (line === false)
                            break;
                        content = parseMagic(config.magic, line).content;
                    }
                    if (line === false)
                        return [3 /*break*/, 10];
                    console.log("Graph found");
                    if (!(content !== null && config.exportFormat && contentIsFile(content))) return [3 /*break*/, 9];
                    diagFile_1 = content;
                    outputFile = outputFileName(config, diagFile_1);
                    return [4 /*yield*/, checkFileExistsFromPath(d, outputFile)];
                case 5:
                    checkExist = _a.sent();
                    rfile = contentToFileName(config, diagFile_1);
                    return [4 /*yield*/, checkFileExistsFromPath(d, rfile)];
                case 6:
                    checkExistRfile = _a.sent();
                    if (!(checkExistRfile && !checkExist)) return [3 /*break*/, 8];
                    return [4 /*yield*/, getContent(d, config, diagFile_1)];
                case 7:
                    data = _a.sent();
                    return [2 /*return*/, { diagFile: diagFile_1, index: index, content: data,
                            onlyExternalFile: true }];
                case 8:
                    if (!checkExistRfile)
                        console.log("File " + rfile + " doesn't exist.");
                    _a.label = 9;
                case 9:
                    remainder = config.prefixes;
                    while (remainder !== null && remainder.length > 0) {
                        line = readLine(file_lines);
                        if (line === false)
                            // EOF
                            break;
                        remainder = parsePrefix(line, remainder);
                    }
                    return [3 /*break*/, 4];
                case 10:
                    if (!((remainder === null || remainder.length > 0) && content !== null)) {
                        return [2 /*return*/, false];
                    }
                    console.log("do something with " + content);
                    diagFile = null;
                    if (!contentIsFile(content)) return [3 /*break*/, 12];
                    diagFile = content;
                    return [4 /*yield*/, getContent(d, config, content)];
                case 11:
                    content = _a.sent();
                    _a.label = 12;
                case 12:
                    handleConfig = { content: content, diagFile: diagFile, index: index, onlyExternalFile: false };
                    return [2 /*return*/, handleConfig];
            }
        });
    });
}
/* ****************



maintenant on traite l'aspect websocket




***************** */
var expectedIdFromServer = 0;
function logExpectedId() {
    console.log("expectedId: ");
    console.log(expectedIdFromServer);
}
function requestSnapshot(ws) {
    var msg = null;
    sendDataOnSocket(ws, {
        snapshot: false,
        break: false,
        history: false,
        broadcast: false,
        msg: msg
    });
}
function handleServerToClientMsg(ws, snapshotRequest, normalRequest, data) {
    var msg = JSON.parse(data);
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
    var diffs = [];
    for (var i = 0; i < data.length; i++) {
        var diff = data[i];
        // logExpectedId();
        if (diff.id > expectedIdFromServer && !diff.snapshot) {
            requestSnapshot(ws);
            return [];
        }
        // logExpectedId();
        // console.log("avant");
        expectedIdFromServer = diff.id + 1;
        // console.log("apres");
        // logExpectedId();
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
    // console.log("avant2");
    // logExpectedId();
    var moreData = Object.assign(data, { "expectedId": expectedIdFromServer });
    // {...data, "expectedId" :expectedId};
    // logExpectedId();
    // console.log("sending moredata: ");
    // console.log(moreData);
    sendDiffOnSocket(ws, moreData);
}
function broadcastDataOnSocket(ws, data) {
    sendDataOnSocket(ws, __assign(__assign({}, data), { broadcast: true }));
}
