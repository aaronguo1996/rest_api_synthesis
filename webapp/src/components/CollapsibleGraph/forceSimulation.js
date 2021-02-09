import * as d3 from "d3";

export const graphWidth = 2000;
export const graphHeight = 900;
export const force = d3.forceSimulation()
    .force("charge", d3.forceManyBody().strength(-1000))
    .force("center", d3.forceCenter(graphWidth / 2, graphHeight / 2))
    .force("link", d3.forceLink().id(d => d.key))
    .force("y", d3.forceY(0))
    .force("x", d3.forceX(0));

export const drag = simulation => {

    function dragstarted(event) {
        if (!event.active) simulation.alphaTarget(0.3).restart();
        event.subject.fx = event.subject.x;
        event.subject.fy = event.subject.y;
    }

    function dragged(event) {
        event.subject.fx = event.x;
        event.subject.fy = event.y;
    }

    function dragended(event) {
        if (!event.active) simulation.alphaTarget(0);
        event.subject.fx = null;
        event.subject.fy = null;
    }

    return d3.drag()
        .on("start", dragstarted)
        .on("drag", dragged)
        .on("end", dragended);
};

// export const scale = d3.scaleOrdinal(d3.schemeCategory10);
// export const scale = d3.scaleOrdinal(d3.schemeSet3);
export const scale = d3.scaleOrdinal(d3.schemeTableau10);