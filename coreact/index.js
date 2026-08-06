export class Layer {
    id;
    name;
    parentId;
    color;
    colorEnabled;
    visible;
    constructor(id, name, parentId = null, color = "#3498db", colorEnabled = false, visible = true) {
        this.id = id;
        this.name = name;
        this.parentId = parentId;
        this.color = color;
        this.colorEnabled = colorEnabled;
        this.visible = visible;
    }
}
export class SortStore {
    sorts = new Map();
    constructor() {
        this.registerBuiltInSorts();
    }
    registerBuiltInSorts() {
        this.sorts.set("Equality", {
            name: "Equality",
            dependencies: {},
            attributes: {},
            drawFunction: () => null
        });
    }
    getAllSorts() {
        return Array.from(this.sorts.values());
    }
    newSort(name, dependencies, attributes, drawFunction, // Ensure this returns any
    initContext) {
        // Consistency check: all dependencies must be already defined sorts, unless it's a flag
        for (const [depKey, depSortName] of Object.entries(dependencies)) {
            if (depSortName !== "flag" && !this.sorts.has(depSortName)) {
                throw new Error(`Consistency Check Failed: Dependency sort '${depSortName}' for dependency '${depKey}' in sort '${name}' is not defined.`);
            }
        }
        // Validate attribute types (basic check to ensure they are strings representing types)
        const validTypes = ["number", "string", "boolean", "position"];
        for (const [attrName, attrType] of Object.entries(attributes)) {
            if (!validTypes.includes(attrType)) {
                throw new Error(`Consistency Check Failed: Invalid attribute type '${attrType}' for attribute '${attrName}' in sort '${name}'.`);
            }
        }
        this.sorts.set(name, {
            name,
            dependencies,
            attributes,
            drawFunction,
            initContext
        });
        return this; // Enable chaining
    }
    getSort(name) {
        return this.sorts.get(name);
    }
    clear() {
        this.sorts.clear();
        this.registerBuiltInSorts();
    }
}
export class Artefact {
    sortName;
    dependencies;
    data;
    drawFunction;
    layerId;
    svgElement = null; // Store the rendered SVG node
    constructor(sortName, dependencies, data, drawFunction, layerId = "root") {
        this.sortName = sortName;
        this.dependencies = dependencies;
        this.data = data;
        this.drawFunction = drawFunction;
        this.layerId = layerId;
    }
    getResolvedData() {
        const result = { ...this.data };
        for (const [key, depArtefact] of Object.entries(this.dependencies)) {
            if (typeof depArtefact === "boolean") {
                result[key] = depArtefact; // Just copy flags directly
            }
            else {
                result[key] = depArtefact.getResolvedData();
            }
        }
        return result;
    }
    getSelfAndDependencies() {
        const result = new Set();
        result.add(this);
        for (const depArtefact of Object.values(this.dependencies)) {
            if (typeof depArtefact !== "boolean") {
                for (const nestedDep of depArtefact.getSelfAndDependencies()) {
                    result.add(nestedDep);
                }
            }
        }
        return result;
    }
    draw(context) {
        this.svgElement = this.drawFunction(this.getResolvedData(), context);
    }
}
export class EqualityArtefact extends Artefact {
    children;
    constructor(children, data = {}, layerId = "root") {
        const deps = {};
        children.forEach((child, idx) => {
            deps[`${idx}`] = child;
        });
        super("Equality", deps, data, () => null, layerId);
        this.children = [...children];
    }
    setChildren(newChildren) {
        this.children = [...newChildren];
        const newDeps = {};
        this.children.forEach((child, idx) => {
            newDeps[`${idx}`] = child;
        });
        this.dependencies = newDeps;
    }
}
export class Drawing {
    sortStore;
    artefacts = [];
    layers = new Map();
    focusedLayerId = null;
    constructor(sortStore) {
        this.sortStore = sortStore;
        this.addLayer("root", "Root Layer", null, "#3498db", false);
    }
    addLayer(id, name, parentId = null, color = "#3498db", colorEnabled = false, visible = true) {
        if (this.layers.has(id)) {
            throw new Error(`Layer with id '${id}' already exists.`);
        }
        if (parentId !== null && !this.layers.has(parentId)) {
            throw new Error(`Parent layer '${parentId}' does not exist.`);
        }
        const layer = new Layer(id, name, parentId, color, colorEnabled, visible);
        this.layers.set(id, layer);
        return layer;
    }
    isLayerVisible(layerId) {
        let current = layerId;
        while (current && this.layers.has(current)) {
            const layer = this.layers.get(current);
            if (!layer.visible) {
                return false;
            }
            current = layer.parentId;
        }
        return true;
    }
    getLayer(id) {
        return this.layers.get(id);
    }
    getAllLayers() {
        return Array.from(this.layers.values());
    }
    getFocusedLayerId() {
        return this.focusedLayerId;
    }
    setFocusedLayer(id) {
        if (id !== null && !this.layers.has(id)) {
            throw new Error(`Layer '${id}' does not exist.`);
        }
        this.focusedLayerId = id;
    }
    getAncestors(layerId) {
        const ancestors = new Set();
        let current = layerId;
        while (current && this.layers.has(current)) {
            ancestors.add(current);
            const layer = this.layers.get(current);
            current = layer.parentId;
        }
        return ancestors;
    }
    getDescendants(layerId) {
        const descendants = new Set();
        descendants.add(layerId);
        let addedNew = true;
        while (addedNew) {
            addedNew = false;
            for (const layer of this.layers.values()) {
                if (layer.parentId && descendants.has(layer.parentId) && !descendants.has(layer.id)) {
                    descendants.add(layer.id);
                    addedNew = true;
                }
            }
        }
        return descendants;
    }
    removeLayer(layerId) {
        if (!this.layers.has(layerId))
            return;
        const descendants = this.getDescendants(layerId);
        // Remove all artefacts in any of these layers
        this.artefacts = this.artefacts.filter(art => !descendants.has(art.layerId));
        // Remove the layers
        for (const id of descendants) {
            this.layers.delete(id);
        }
        if (this.focusedLayerId && descendants.has(this.focusedLayerId)) {
            this.focusedLayerId = null;
        }
        // If all layers were deleted, re-create default root layer
        if (this.layers.size === 0) {
            this.addLayer("root", "Root Layer", null, "#3498db", false);
        }
    }
    setArtefactLayer(artefact, targetLayerId) {
        if (!this.layers.has(targetLayerId)) {
            throw new Error(`Layer '${targetLayerId}' does not exist.`);
        }
        const allowedAncestors = this.getAncestors(targetLayerId);
        // Check artefact's dependencies
        for (const [depKey, depVal] of Object.entries(artefact.dependencies)) {
            if (typeof depVal !== "boolean") {
                if (!allowedAncestors.has(depVal.layerId)) {
                    const depLayerName = this.layers.get(depVal.layerId)?.name || depVal.layerId;
                    const targetLayerName = this.layers.get(targetLayerId)?.name || targetLayerId;
                    throw new Error(`Consistency Check Failed: Dependency '${depKey}' (in layer '${depLayerName}') is not in layer '${targetLayerName}' or any of its lower ancestor layers.`);
                }
            }
        }
        // Check artefacts that depend on this artefact
        for (const otherArt of this.artefacts) {
            if (otherArt === artefact)
                continue;
            for (const depVal of Object.values(otherArt.dependencies)) {
                if (depVal === artefact) {
                    const otherAllowed = this.getAncestors(otherArt.layerId);
                    if (!otherAllowed.has(targetLayerId)) {
                        const targetLayerName = this.layers.get(targetLayerId)?.name || targetLayerId;
                        const otherLayerName = this.layers.get(otherArt.layerId)?.name || otherArt.layerId;
                        throw new Error(`Consistency Check Failed: Artefact '${otherArt.data.label || otherArt.sortName}' (in layer '${otherLayerName}') depends on this artefact, but layer '${targetLayerName}' is not in its lower ancestor layers.`);
                    }
                }
            }
        }
        if (artefact.sortName === "Equality") {
            const children = artefact instanceof EqualityArtefact
                ? artefact.children
                : Object.values(artefact.dependencies).filter((v) => typeof v !== "boolean");
            // Validate equality dependencies for the target layer
            this.validateEqualityDependencies(children, targetLayerId);
            artefact.layerId = targetLayerId;
            // Trigger same-layer merging if there are overlapping equality artefacts on targetLayerId
            const sameLayerEqualities = this.artefacts.filter(art => art !== artefact && (art instanceof EqualityArtefact || art.sortName === "Equality") && art.layerId === targetLayerId);
            const childrenSet = new Set(children);
            const overlapping = sameLayerEqualities.filter(art => {
                const cList = art instanceof EqualityArtefact
                    ? art.children
                    : Object.values(art.dependencies).filter((v) => typeof v !== "boolean");
                return cList.some(c => childrenSet.has(c));
            });
            if (overlapping.length > 0) {
                const combinedSet = new Set(children);
                for (const ov of overlapping) {
                    const cList = ov instanceof EqualityArtefact
                        ? ov.children
                        : Object.values(ov.dependencies).filter((v) => typeof v !== "boolean");
                    cList.forEach(c => combinedSet.add(c));
                }
                const combined = Array.from(combinedSet);
                this.validateEqualityDependencies(combined, targetLayerId);
                if (artefact instanceof EqualityArtefact) {
                    artefact.setChildren(combined);
                }
                for (const ov of overlapping) {
                    this.artefacts = this.artefacts.filter(a => a !== ov);
                }
            }
        }
        else {
            artefact.layerId = targetLayerId;
        }
    }
    getLayersTopological() {
        const result = [];
        const visited = new Set();
        const visit = (layerId) => {
            if (visited.has(layerId))
                return;
            const layer = this.layers.get(layerId);
            if (!layer)
                return;
            if (layer.parentId && this.layers.has(layer.parentId) && !visited.has(layer.parentId)) {
                visit(layer.parentId);
            }
            visited.add(layerId);
            result.push(layer);
        };
        for (const layerId of this.layers.keys()) {
            visit(layerId);
        }
        return result;
    }
    areEqual(a, b, layerId) {
        if (a === b)
            return true;
        const allowedAncestors = this.getAncestors(layerId);
        const adj = new Map();
        for (const art of this.artefacts) {
            if (art.sortName === "Equality" && allowedAncestors.has(art.layerId)) {
                let children = [];
                if (art instanceof EqualityArtefact) {
                    children = art.children;
                }
                else {
                    children = Object.values(art.dependencies).filter((v) => typeof v !== "boolean");
                }
                for (let i = 0; i < children.length; i++) {
                    for (let j = i + 1; j < children.length; j++) {
                        const c1 = children[i];
                        const c2 = children[j];
                        if (!adj.has(c1))
                            adj.set(c1, new Set());
                        if (!adj.has(c2))
                            adj.set(c2, new Set());
                        adj.get(c1).add(c2);
                        adj.get(c2).add(c1);
                    }
                }
            }
        }
        if (!adj.has(a))
            return false;
        const visited = new Set();
        const queue = [a];
        visited.add(a);
        while (queue.length > 0) {
            const current = queue.shift();
            if (current === b)
                return true;
            const neighbors = adj.get(current);
            if (neighbors) {
                for (const neighbor of neighbors) {
                    if (!visited.has(neighbor)) {
                        visited.add(neighbor);
                        queue.push(neighbor);
                    }
                }
            }
        }
        return false;
    }
    validateEqualityDependencies(artefacts, layerId) {
        const uniqueArtefacts = Array.from(new Set(artefacts));
        if (uniqueArtefacts.length < 2) {
            throw new Error("Consistency Check Failed: An equality artefact must connect at least two distinct artefacts.");
        }
        const allowedAncestors = this.getAncestors(layerId);
        // 1. Validate sort uniformity & layer hierarchy
        const firstSort = uniqueArtefacts[0].sortName;
        for (const art of uniqueArtefacts) {
            if (art.sortName !== firstSort) {
                throw new Error(`Consistency Check Failed: All artefacts in an equality artefact must be of the same sort. Found '${firstSort}' and '${art.sortName}'.`);
            }
            if (!allowedAncestors.has(art.layerId)) {
                const artLayerName = this.layers.get(art.layerId)?.name || art.layerId;
                const targetLayerName = this.layers.get(layerId)?.name || layerId;
                throw new Error(`Consistency Check Failed: Artefact '${art.data.label || art.sortName}' (in layer '${artLayerName}') is not in layer '${targetLayerName}' or any of its lower ancestor layers.`);
            }
        }
        // 2. Pairwise dependency check against first artefact
        const sortDef = this.sortStore.getSort(firstSort);
        if (!sortDef) {
            throw new Error(`Consistency Check Failed: Sort '${firstSort}' is not defined.`);
        }
        const firstArt = uniqueArtefacts[0];
        for (let i = 1; i < uniqueArtefacts.length; i++) {
            const otherArt = uniqueArtefacts[i];
            for (const [depKey, depSortName] of Object.entries(sortDef.dependencies)) {
                const firstDep = firstArt.dependencies[depKey];
                const otherDep = otherArt.dependencies[depKey];
                if (depSortName === "flag") {
                    if (firstDep !== otherDep) {
                        throw new Error(`Consistency Check Failed: Flag dependency '${depKey}' differs between artefacts in equality artefact.`);
                    }
                }
                else {
                    if (!firstDep || typeof firstDep === "boolean" || !otherDep || typeof otherDep === "boolean") {
                        throw new Error(`Consistency Check Failed: Missing artefact dependency '${depKey}' for equality check.`);
                    }
                    if (!this.areEqual(firstDep, otherDep, layerId)) {
                        throw new Error(`Consistency Check Failed: Dependencies '${depKey}' of artefacts '${firstArt.data.label || firstArt.sortName}' and '${otherArt.data.label || otherArt.sortName}' are not equal at layer '${layerId}'.`);
                    }
                }
            }
        }
    }
    newEqualityArtefact(artefacts, layerId, data = {}) {
        const targetLayerId = layerId || (this.layers.size > 0 ? Array.from(this.layers.keys())[0] : "root");
        if (!this.layers.has(targetLayerId)) {
            throw new Error(`Consistency Check Failed: Layer '${targetLayerId}' does not exist.`);
        }
        const inputSet = new Set(artefacts);
        if (inputSet.size < 2) {
            throw new Error("Consistency Check Failed: An equality artefact must connect at least two distinct artefacts.");
        }
        // Search for overlapping equality artefacts on the exact SAME layer
        const sameLayerEqualities = this.artefacts.filter(art => (art instanceof EqualityArtefact || art.sortName === "Equality") && art.layerId === targetLayerId);
        const overlapping = [];
        for (const eq of sameLayerEqualities) {
            const children = eq instanceof EqualityArtefact
                ? eq.children
                : Object.values(eq.dependencies).filter((v) => typeof v !== "boolean");
            if (children.some(c => inputSet.has(c))) {
                overlapping.push(eq);
            }
        }
        if (overlapping.length > 0) {
            const combinedChildrenSet = new Set(inputSet);
            for (const eq of overlapping) {
                const children = eq instanceof EqualityArtefact
                    ? eq.children
                    : Object.values(eq.dependencies).filter((v) => typeof v !== "boolean");
                children.forEach(c => combinedChildrenSet.add(c));
            }
            const combinedChildren = Array.from(combinedChildrenSet);
            this.validateEqualityDependencies(combinedChildren, targetLayerId);
            const mainEq = overlapping[0];
            let resultEq;
            if (mainEq instanceof EqualityArtefact) {
                mainEq.setChildren(combinedChildren);
                Object.assign(mainEq.data, data);
                resultEq = mainEq;
            }
            else {
                const idx = this.artefacts.indexOf(mainEq);
                resultEq = new EqualityArtefact(combinedChildren, { ...mainEq.data, ...data }, targetLayerId);
                if (idx !== -1)
                    this.artefacts[idx] = resultEq;
            }
            for (let i = 1; i < overlapping.length; i++) {
                const toRemove = overlapping[i];
                this.artefacts = this.artefacts.filter(a => a !== toRemove);
            }
            return resultEq;
        }
        else {
            const initialChildren = Array.from(inputSet);
            this.validateEqualityDependencies(initialChildren, targetLayerId);
            const newEq = new EqualityArtefact(initialChildren, data, targetLayerId);
            this.artefacts.push(newEq);
            return newEq;
        }
    }
    newArtefact(sortName, dependencies, data, layerId) {
        if (sortName === "Equality") {
            const children = [];
            if (Array.isArray(data.children)) {
                children.push(...data.children);
            }
            else {
                for (const val of Object.values(dependencies)) {
                    if (val && typeof val !== "boolean") {
                        children.push(val);
                    }
                }
            }
            return this.newEqualityArtefact(children, layerId, data);
        }
        const sortDef = this.sortStore.getSort(sortName);
        if (!sortDef) {
            throw new Error(`Consistency Check Failed: Sort '${sortName}' is not defined.`);
        }
        const targetLayerId = layerId || (this.layers.size > 0 ? Array.from(this.layers.keys())[0] : "root");
        if (!this.layers.has(targetLayerId)) {
            throw new Error(`Consistency Check Failed: Layer '${targetLayerId}' does not exist.`);
        }
        const allowedAncestors = this.getAncestors(targetLayerId);
        // 1. Validate Dependencies
        for (const [depKey, expectedSortName] of Object.entries(sortDef.dependencies)) {
            const providedValue = dependencies[depKey];
            if (expectedSortName === "flag") {
                if (providedValue !== undefined && typeof providedValue !== "boolean") {
                    throw new Error(`Consistency Check Failed: Dependency '${depKey}' expected flag (boolean), but got '${typeof providedValue}'.`);
                }
            }
            else {
                if (!providedValue || typeof providedValue === "boolean") {
                    throw new Error(`Consistency Check Failed: Missing dependency '${depKey}' for artefact of sort '${sortName}'.`);
                }
                if (providedValue.sortName !== expectedSortName) {
                    throw new Error(`Consistency Check Failed: Dependency '${depKey}' expected sort '${expectedSortName}', but got '${providedValue.sortName}'.`);
                }
                // Hierarchy validation: dependency layer must be in allowedAncestors
                if (!allowedAncestors.has(providedValue.layerId)) {
                    const depLayerName = this.layers.get(providedValue.layerId)?.name || providedValue.layerId;
                    const targetLayerName = this.layers.get(targetLayerId)?.name || targetLayerId;
                    throw new Error(`Consistency Check Failed: Dependency '${depKey}' (in layer '${depLayerName}') is not in layer '${targetLayerName}' or any of its lower ancestor layers.`);
                }
            }
        }
        // Verify no extra unexpected dependencies were provided
        for (const providedKey of Object.keys(dependencies)) {
            if (!sortDef.dependencies[providedKey]) {
                throw new Error(`Consistency Check Failed: Unexpected dependency '${providedKey}' provided for artefact of sort '${sortName}'.`);
            }
        }
        // 2. Validate Data Attributes (Strict Check)
        for (const [attrName, expectedType] of Object.entries(sortDef.attributes)) {
            const value = data[attrName];
            if (value === undefined) {
                throw new Error(`Consistency Check Failed: Missing data attribute '${attrName}' for artefact of sort '${sortName}'.`);
            }
            // Primitive type checking
            if (expectedType === "position") {
                if (!Array.isArray(value) || value.length !== 2 || typeof value[0] !== "number" || typeof value[1] !== "number") {
                    throw new Error(`Consistency Check Failed: Data attribute '${attrName}' expected to be of primitive type 'position' ([number, number]), but got ${JSON.stringify(value)}.`);
                }
            }
            else if (typeof value !== expectedType) {
                throw new Error(`Consistency Check Failed: Data attribute '${attrName}' expected to be '${expectedType}', but got '${typeof value}'.`);
            }
        }
        // Check for unexpected properties
        for (const key of Object.keys(data)) {
            if (key === "label") {
                if (typeof data[key] !== "string") {
                    throw new Error(`Consistency Check Failed: Data attribute 'label' expected to be 'string', but got '${typeof data[key]}'.`);
                }
            }
            else if (sortDef.attributes[key] === undefined) {
                throw new Error(`Consistency Check Failed: Unexpected data attribute '${key}' provided for sort '${sortName}'.`);
            }
        }
        const artefact = new Artefact(sortName, dependencies, data, sortDef.drawFunction, targetLayerId);
        this.artefacts.push(artefact);
        return artefact;
    }
    draw(context) {
        // 1. Initialize context for all defined sorts (e.g., for SVG defs/markers)
        for (const sortDef of this.sortStore.getAllSorts()) {
            if (sortDef.initContext) {
                sortDef.initContext(context);
            }
        }
        // 2. Draw layers in topological order
        const orderedLayers = this.getLayersTopological();
        for (const layer of orderedLayers) {
            const layerGroup = context.append("g")
                .attr("class", "layer-group")
                .attr("data-layer-id", layer.id);
            if (!this.isLayerVisible(layer.id)) {
                layerGroup.attr("display", "none");
            }
            // Set Opacity based on Focus
            if (this.focusedLayerId !== null) {
                const opacity = (layer.id === this.focusedLayerId) ? 1.0 : 0.5;
                layerGroup.attr("opacity", opacity);
            }
            else {
                layerGroup.attr("opacity", 1.0);
            }
            // Draw artefacts belonging to this layer
            const layerArtefacts = this.artefacts.filter(a => a.layerId === layer.id);
            for (const artefact of layerArtefacts) {
                artefact.draw(layerGroup);
            }
            // Apply partial layer color if colorEnabled
            if (layer.colorEnabled && layer.color) {
                layerGroup.classed("layer-colored", true);
                layerGroup.selectAll("line, path").attr("stroke", layer.color);
                layerGroup.selectAll("circle").attr("stroke", layer.color).attr("fill", layer.color);
            }
        }
    }
    getArtefacts() {
        return this.artefacts;
    }
    removeArtefact(target) {
        this.artefacts = this.artefacts.filter(art => !art.getSelfAndDependencies().has(target));
        // Remove any equality artefacts whose children count fell below 2
        this.artefacts = this.artefacts.filter(art => {
            if (art.sortName === "Equality") {
                const children = art instanceof EqualityArtefact
                    ? art.children
                    : Object.values(art.dependencies).filter((v) => typeof v !== "boolean");
                return children.length >= 2;
            }
            return true;
        });
    }
    removeEqualityChild(eq, childToRemove) {
        if (eq.sortName !== "Equality")
            return;
        const currentChildren = eq instanceof EqualityArtefact
            ? eq.children
            : Object.values(eq.dependencies).filter((v) => typeof v !== "boolean");
        const remaining = currentChildren.filter(c => c !== childToRemove);
        if (remaining.length < 2) {
            this.artefacts = this.artefacts.filter(art => art !== eq);
        }
        else {
            if (eq instanceof EqualityArtefact) {
                eq.setChildren(remaining);
            }
            else {
                const newDeps = {};
                remaining.forEach((child, idx) => {
                    newDeps[`${idx}`] = child;
                });
                eq.dependencies = newDeps;
            }
        }
    }
    areDependenciesEqual(a1, a2) {
        if (a1.sortName !== a2.sortName) {
            return false;
        }
        const keys1 = Object.keys(a1.dependencies);
        const keys2 = Object.keys(a2.dependencies);
        if (keys1.length !== keys2.length) {
            return false;
        }
        for (const k of keys1) {
            if (!Object.prototype.hasOwnProperty.call(a2.dependencies, k)) {
                return false;
            }
            if (a1.dependencies[k] !== a2.dependencies[k]) {
                return false;
            }
        }
        return true;
    }
    areProvablyEqual(a, b) {
        return this.areEqual(a, b, a.layerId) || this.areEqual(a, b, b.layerId);
    }
    mergeArtefacts(a1, a2) {
        if (!this.artefacts.includes(a1) || !this.artefacts.includes(a2)) {
            throw new Error("Consistency Check Failed: Both artefacts must exist in the drawing to be merged.");
        }
        if (a1 === a2) {
            throw new Error("Consistency Check Failed: Cannot merge an artefact with itself.");
        }
        if (!this.areDependenciesEqual(a1, a2)) {
            throw new Error("Consistency Check Failed: Cannot merge artefacts with different dependencies or sorts.");
        }
        // Layer hierarchy check: any artefact depending on a1 must allow a2's layerId in its ancestors
        const allowedForA2Layer = a2.layerId;
        for (const art of this.artefacts) {
            if (art === a1 || art === a2)
                continue;
            for (const depVal of Object.values(art.dependencies)) {
                if (depVal === a1) {
                    const artAllowed = this.getAncestors(art.layerId);
                    if (!artAllowed.has(allowedForA2Layer)) {
                        const a2LayerName = this.layers.get(allowedForA2Layer)?.name || allowedForA2Layer;
                        const artLayerName = this.layers.get(art.layerId)?.name || art.layerId;
                        throw new Error(`Consistency Check Failed: Merging would violate layer hierarchy. Artefact '${art.data.label || art.sortName}' (in layer '${artLayerName}') depends on this artefact, but target layer '${a2LayerName}' is not in its lower ancestor layers.`);
                    }
                }
            }
        }
        // Determine new label: concatenation of old labels separated by ", "
        const label1 = typeof a1.data.label === "string" ? a1.data.label.trim() : "";
        const label2 = typeof a2.data.label === "string" ? a2.data.label.trim() : "";
        let combinedLabel = "";
        if (label1 && label2) {
            combinedLabel = `${label1}, ${label2}`;
        }
        else if (label1) {
            combinedLabel = label1;
        }
        else if (label2) {
            combinedLabel = label2;
        }
        // Keep second artefact's datafields and set combined label
        if (combinedLabel) {
            a2.data.label = combinedLabel;
        }
        else {
            delete a2.data.label;
        }
        // Replace references to a1 with a2 in all artefacts
        for (const art of this.artefacts) {
            if (art === a1)
                continue;
            for (const [depKey, depVal] of Object.entries(art.dependencies)) {
                if (depVal === a1) {
                    art.dependencies[depKey] = a2;
                }
            }
            if (art.sortName === "Equality") {
                const currentChildren = art instanceof EqualityArtefact
                    ? art.children
                    : Object.values(art.dependencies).filter((v) => typeof v !== "boolean");
                const updatedChildren = currentChildren.map(c => c === a1 ? a2 : c);
                const uniqueChildren = Array.from(new Set(updatedChildren));
                if (art instanceof EqualityArtefact) {
                    art.setChildren(uniqueChildren);
                }
                else {
                    const newDeps = {};
                    uniqueChildren.forEach((child, idx) => {
                        newDeps[`${idx}`] = child;
                    });
                    art.dependencies = newDeps;
                }
            }
        }
        // Clean up any equality artefacts that now have fewer than 2 distinct children
        this.artefacts = this.artefacts.filter(art => {
            if (art.sortName === "Equality") {
                const children = art instanceof EqualityArtefact
                    ? art.children
                    : Object.values(art.dependencies).filter((v) => typeof v !== "boolean");
                return children.length >= 2;
            }
            return true;
        });
        // Remove a1 from drawing
        this.artefacts = this.artefacts.filter(art => art !== a1);
        return a2;
    }
    clear(keepDefaultRoot = true) {
        this.artefacts = [];
        this.layers.clear();
        this.focusedLayerId = null;
        if (keepDefaultRoot) {
            this.addLayer("root", "Root Layer", null, "#3498db", false);
        }
    }
}
export class DrawingStore {
    drawings = new Map();
    checkIsRule(drawing) {
        const layers = drawing.getAllLayers();
        const rootLayers = layers.filter(l => l.parentId === null);
        // Rule condition 1: At most one root layer
        if (rootLayers.length > 1) {
            return {
                isRule: false,
                reason: `Drawing has ${rootLayers.length} root layers (at most 1 allowed).`
            };
        }
        // Rule condition 2: Depth at most 3
        const getLayerDepth = (layerId) => {
            let depth = 0;
            let current = layerId;
            const visited = new Set();
            while (current) {
                if (visited.has(current))
                    break;
                visited.add(current);
                depth++;
                const layer = drawing.getLayer(current);
                current = layer ? layer.parentId : null;
            }
            return depth;
        };
        for (const layer of layers) {
            const depth = getLayerDepth(layer.id);
            if (depth > 3) {
                return {
                    isRule: false,
                    reason: `Layer '${layer.name}' exceeds maximum allowed depth of 3 (current depth: ${depth}).`
                };
            }
        }
        // Rule condition 3: Exactly one child of the root layer that does not have any children
        if (rootLayers.length === 0) {
            return {
                isRule: false,
                reason: "Drawing has no root layer (a rule requires exactly one child of the root layer with no children)."
            };
        }
        const root = rootLayers[0];
        const rootChildren = layers.filter(l => l.parentId === root.id);
        const leafRootChildren = rootChildren.filter(child => {
            const childrenOfChild = layers.filter(l => l.parentId === child.id);
            return childrenOfChild.length === 0;
        });
        if (leafRootChildren.length !== 1) {
            return {
                isRule: false,
                reason: `Root layer must have exactly 1 child layer without children, but found ${leafRootChildren.length}.`
            };
        }
        return { isRule: true };
    }
    static firstOrderFromLayers(layers) {
        const rootLayers = layers.filter(l => l.parentId === null);
        if (rootLayers.length !== 1) {
            return false;
        }
        const root = rootLayers[0];
        const rootChildren = layers.filter(l => l.parentId === root.id);
        return rootChildren.length === 1;
    }
    checkIsFirstOrder(drawing) {
        if (!this.checkIsRule(drawing).isRule) {
            return false;
        }
        return DrawingStore.firstOrderFromLayers(drawing.getAllLayers());
    }
    saveDrawing(name, drawing) {
        if (!name || !name.trim()) {
            throw new Error("Consistency Check Failed: Drawing name cannot be empty.");
        }
        const trimmedName = name.trim();
        const ruleCheck = this.checkIsRule(drawing);
        const artefacts = drawing.getArtefacts();
        const artefactToId = new Map();
        artefacts.forEach((art, index) => {
            artefactToId.set(art, `art_${index}`);
        });
        const layersData = drawing.getAllLayers().map(l => ({
            id: l.id,
            name: l.name,
            parentId: l.parentId,
            color: l.color,
            colorEnabled: l.colorEnabled,
            visible: l.visible
        }));
        const artefactsData = artefacts.map(art => {
            const serializedDeps = {};
            for (const [key, val] of Object.entries(art.dependencies)) {
                if (typeof val === "boolean") {
                    serializedDeps[key] = val;
                }
                else if (val && artefactToId.has(val)) {
                    serializedDeps[key] = artefactToId.get(val);
                }
            }
            return {
                id: artefactToId.get(art),
                sortName: art.sortName,
                layerId: art.layerId,
                dependencies: serializedDeps,
                data: JSON.parse(JSON.stringify(art.data))
            };
        });
        const savedDrawing = {
            name: trimmedName,
            layers: layersData,
            artefacts: artefactsData,
            isRule: ruleCheck.isRule,
            isFirstOrder: this.checkIsFirstOrder(drawing)
        };
        this.drawings.set(trimmedName, savedDrawing);
        return savedDrawing;
    }
    loadDrawing(name, drawing) {
        const savedDrawing = this.drawings.get(name);
        if (!savedDrawing) {
            throw new Error(`Consistency Check Failed: Drawing '${name}' does not exist.`);
        }
        drawing.clear(false);
        // Restore layers iteratively
        const remainingLayers = [...savedDrawing.layers];
        let layerProgress = true;
        while (remainingLayers.length > 0 && layerProgress) {
            layerProgress = false;
            for (let i = 0; i < remainingLayers.length; i++) {
                const lData = remainingLayers[i];
                if (lData.parentId === null || drawing.getLayer(lData.parentId) !== undefined) {
                    drawing.addLayer(lData.id, lData.name, lData.parentId, lData.color, lData.colorEnabled, lData.visible ?? true);
                    remainingLayers.splice(i, 1);
                    layerProgress = true;
                    break;
                }
            }
        }
        if (remainingLayers.length > 0) {
            throw new Error(`Consistency Check Failed: Could not restore layer hierarchy for drawing '${name}'.`);
        }
        // Restore artefacts iteratively
        const remainingArtefacts = [...savedDrawing.artefacts];
        const createdArtefacts = new Map();
        let artProgress = true;
        while (remainingArtefacts.length > 0 && artProgress) {
            artProgress = false;
            for (let i = 0; i < remainingArtefacts.length; i++) {
                const artData = remainingArtefacts[i];
                let ready = true;
                const resolvedDeps = {};
                for (const [depKey, depVal] of Object.entries(artData.dependencies)) {
                    if (typeof depVal === "boolean") {
                        resolvedDeps[depKey] = depVal;
                    }
                    else if (typeof depVal === "string") {
                        if (createdArtefacts.has(depVal)) {
                            resolvedDeps[depKey] = createdArtefacts.get(depVal);
                        }
                        else {
                            ready = false;
                            break;
                        }
                    }
                }
                if (ready) {
                    const newArt = drawing.newArtefact(artData.sortName, resolvedDeps, artData.data, artData.layerId);
                    createdArtefacts.set(artData.id, newArt);
                    remainingArtefacts.splice(i, 1);
                    artProgress = true;
                    break;
                }
            }
        }
        if (remainingArtefacts.length > 0) {
            throw new Error(`Consistency Check Failed: Could not resolve dependencies for drawing '${name}'.`);
        }
        savedDrawing.isRule = this.checkIsRule(drawing).isRule;
        savedDrawing.isFirstOrder = this.checkIsFirstOrder(drawing);
    }
    exportDrawingJSON(name) {
        const savedDrawing = this.drawings.get(name);
        if (!savedDrawing) {
            throw new Error(`Consistency Check Failed: Drawing '${name}' does not exist.`);
        }
        return JSON.stringify(savedDrawing, null, 2);
    }
    importDrawingJSON(jsonString) {
        let parsed;
        try {
            parsed = JSON.parse(jsonString);
        }
        catch (err) {
            throw new Error(`Consistency Check Failed: Invalid JSON format: ${err.message}`);
        }
        if (!parsed || typeof parsed !== "object") {
            throw new Error("Consistency Check Failed: Invalid JSON structure for drawing.");
        }
        if (!parsed.name || typeof parsed.name !== "string" || !parsed.name.trim()) {
            throw new Error("Consistency Check Failed: Missing or invalid 'name' attribute in imported drawing.");
        }
        if (!Array.isArray(parsed.layers)) {
            throw new Error("Consistency Check Failed: Missing or invalid 'layers' array in imported drawing.");
        }
        if (!Array.isArray(parsed.artefacts)) {
            throw new Error("Consistency Check Failed: Missing or invalid 'artefacts' array in imported drawing.");
        }
        const trimmedName = parsed.name.trim();
        // Validate layer structures
        for (const layer of parsed.layers) {
            if (!layer || typeof layer.id !== "string" || typeof layer.name !== "string") {
                throw new Error("Consistency Check Failed: Invalid layer structure in imported drawing.");
            }
        }
        // Validate artefact structures
        for (const art of parsed.artefacts) {
            if (!art || typeof art.id !== "string" || typeof art.sortName !== "string" || typeof art.layerId !== "string" || !art.dependencies || typeof art.dependencies !== "object" || !art.data || typeof art.data !== "object") {
                throw new Error("Consistency Check Failed: Invalid artefact structure in imported drawing.");
            }
        }
        const savedDrawing = {
            name: trimmedName,
            layers: parsed.layers,
            artefacts: parsed.artefacts,
            isRule: !!parsed.isRule,
            isFirstOrder: !!parsed.isRule && DrawingStore.firstOrderFromLayers(parsed.layers)
        };
        this.drawings.set(trimmedName, savedDrawing);
        return savedDrawing;
    }
    getDrawing(name) {
        return this.drawings.get(name);
    }
    getAllDrawings() {
        return Array.from(this.drawings.values());
    }
    deleteDrawing(name) {
        return this.drawings.delete(name);
    }
    clear() {
        this.drawings.clear();
    }
}
function extractEqualityConstraints(rule) {
    return rule.getArtefacts()
        .filter(a => a.sortName === "Equality")
        .map(a => ({
        children: a instanceof EqualityArtefact
            ? a.children
            : Object.values(a.dependencies).filter((v) => typeof v !== "boolean")
    }))
        .filter(c => c.children.length >= 2);
}
function findRuleApplicationsInternal(host, patternArts, equalityConstraints) {
    const results = [];
    if (patternArts.length === 0) {
        return results;
    }
    const patternSet = new Set(patternArts);
    const applicableConstraints = equalityConstraints
        .filter(c => c.children.every(child => patternSet.has(child)));
    const rootLayerIds = host.getAllLayers()
        .filter(l => l.parentId === null)
        .map(l => l.id);
    const hostCandidates = host.getArtefacts().filter(a => rootLayerIds.includes(a.layerId));
    const ordered = [];
    const orderedSet = new Set();
    while (ordered.length < patternArts.length) {
        const next = patternArts.find(a => !orderedSet.has(a) &&
            Object.values(a.dependencies).every(dep => typeof dep === "boolean" || !patternSet.has(dep) || orderedSet.has(dep)));
        if (!next)
            break;
        ordered.push(next);
        orderedSet.add(next);
    }
    const assignment = new Map();
    const used = new Set();
    const checkEqualityConstraints = () => {
        for (const c of applicableConstraints) {
            const imgs = [];
            for (const child of c.children) {
                const img = assignment.get(child);
                if (!img)
                    return false;
                imgs.push(img);
            }
            for (let i = 1; i < imgs.length; i++) {
                if (!host.areEqual(imgs[0], imgs[i], imgs[0].layerId)) {
                    return false;
                }
            }
        }
        return true;
    };
    const backtrack = (i) => {
        if (i === ordered.length) {
            if (checkEqualityConstraints()) {
                results.push({ matchedArtefacts: new Map(assignment) });
            }
            return;
        }
        const a = ordered[i];
        for (const cand of hostCandidates) {
            if (cand.sortName !== a.sortName || used.has(cand))
                continue;
            let ok = true;
            for (const [k, dep] of Object.entries(a.dependencies)) {
                if (typeof dep === "boolean") {
                    if (dep === true && cand.dependencies[k] !== true) {
                        ok = false;
                        break;
                    }
                }
                else if (patternSet.has(dep)) {
                    const img = assignment.get(dep);
                    if (img === undefined || cand.dependencies[k] !== img) {
                        ok = false;
                        break;
                    }
                }
            }
            if (!ok)
                continue;
            assignment.set(a, cand);
            used.add(cand);
            backtrack(i + 1);
            used.delete(cand);
            assignment.delete(a);
        }
    };
    backtrack(0);
    return results;
}
export function findRuleApplications(rule, host) {
    const patternArts = rule.getArtefacts().filter(a => a.sortName !== "Equality");
    return findRuleApplicationsInternal(host, patternArts, extractEqualityConstraints(rule));
}
export function findFirstOrderRuleApplications(rule, host) {
    const layers = rule.getAllLayers();
    const rootLayers = layers.filter(l => l.parentId === null);
    if (rootLayers.length !== 1) {
        return [];
    }
    const root = rootLayers[0];
    const childLayers = layers.filter(l => l.parentId === root.id);
    if (childLayers.length !== 1) {
        return [];
    }
    const rootArts = rule.getArtefacts().filter(a => a.sortName !== "Equality" && a.layerId === root.id);
    return findRuleApplicationsInternal(host, rootArts, extractEqualityConstraints(rule));
}
export function applyFirstOrderRule(rule, host, application) {
    const layers = rule.getAllLayers();
    const rootLayers = layers.filter(l => l.parentId === null);
    if (rootLayers.length !== 1) {
        throw new Error("Consistency Check Failed: Applying a first-order rule requires the rule to have exactly one root layer.");
    }
    const ruleRoot = rootLayers[0];
    const childLayers = layers.filter(l => l.parentId === ruleRoot.id);
    if (childLayers.length !== 1) {
        throw new Error("Consistency Check Failed: Applying a first-order rule requires the rule's root layer to have exactly one child layer.");
    }
    const childLayer = childLayers[0];
    const childArts = rule.getArtefacts()
        .filter(a => a.layerId === childLayer.id && a.sortName !== "Equality");
    const match = application.matchedArtefacts;
    const hostRoots = host.getAllLayers().filter(l => l.parentId === null);
    if (hostRoots.length === 0) {
        throw new Error("Consistency Check Failed: Host drawing has no root layer to add artefacts to.");
    }
    const anchorLayerIds = new Set();
    for (const a of childArts) {
        for (const dep of Object.values(a.dependencies)) {
            if (typeof dep !== "boolean" && dep.layerId === ruleRoot.id && match.has(dep)) {
                anchorLayerIds.add(match.get(dep).layerId);
            }
        }
    }
    let hostRootId;
    if (anchorLayerIds.size === 0) {
        hostRootId = hostRoots[0].id;
    }
    else if (anchorLayerIds.size === 1) {
        hostRootId = Array.from(anchorLayerIds)[0];
    }
    else {
        throw new Error("Consistency Check Failed: Matched artefacts span multiple root layers; cannot determine target layer.");
    }
    const created = new Map();
    const result = [];
    const remaining = [...childArts];
    while (remaining.length > 0) {
        const idx = remaining.findIndex(a => Object.values(a.dependencies).every(dep => typeof dep === "boolean" ||
            (dep.layerId === ruleRoot.id && match.has(dep)) ||
            (dep.layerId === childLayer.id && created.has(dep))));
        if (idx === -1) {
            const unresolved = remaining.find(a => {
                for (const dep of Object.values(a.dependencies)) {
                    if (typeof dep === "boolean")
                        continue;
                    if (dep.layerId === ruleRoot.id && match.has(dep))
                        continue;
                    if (dep.layerId === childLayer.id && created.has(dep))
                        continue;
                    return true;
                }
                return false;
            });
            const label = unresolved ? (unresolved.data.label || unresolved.sortName) : "unknown";
            throw new Error(`Consistency Check Failed: Cannot resolve dependencies when applying first-order rule (artefact '${label}').`);
        }
        const a = remaining.splice(idx, 1)[0];
        const newDeps = {};
        for (const [key, dep] of Object.entries(a.dependencies)) {
            if (typeof dep === "boolean") {
                newDeps[key] = dep;
            }
            else if (dep.layerId === ruleRoot.id) {
                const img = match.get(dep);
                if (!img) {
                    throw new Error(`Consistency Check Failed: No match found for rule artefact '${dep.data.label || dep.sortName}'.`);
                }
                newDeps[key] = img;
            }
            else {
                const copy = created.get(dep);
                if (!copy) {
                    throw new Error(`Consistency Check Failed: No copy created for rule artefact '${dep.data.label || dep.sortName}'.`);
                }
                newDeps[key] = copy;
            }
        }
        const newArt = host.newArtefact(a.sortName, newDeps, JSON.parse(JSON.stringify(a.data)), hostRootId);
        created.set(a, newArt);
        result.push(newArt);
    }
    return result;
}
