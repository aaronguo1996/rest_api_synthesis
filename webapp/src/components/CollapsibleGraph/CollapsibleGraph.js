import React from "react";
import ReactDOM from "react-dom";
import { connect } from "react-redux";
// import _ from "underscore";
import * as d3 from "d3";
import { force, graphWidth, graphHeight, scale, drag } from "./forceSimulation"
import { changeChildrenVisibility } from "../../actions";

class CollapsibleGraph extends React.Component {
    
    getVisibleNodes() {
        const {nodes} = this.props;
        const nodeMap = new Map(nodes.map(v => [v.key, v]));
        const getInvisibleChildren = (v) => {
            // hide all the children nodes if the parent is hidden
            // but do not modify the internal states
            if(v.isVisible) {
                return [];
            }

            const invisibleChildren = v.children.map(c => {
                return getInvisibleChildren(nodeMap.get(c));
            });
            return v.children.concat(invisibleChildren.flat());
        }

        const visibleNodes = nodes.filter(v => v.isVisible);
        const invisibleNodes = nodes.filter(v => !v.isVisible);
        const invisibleChildren = invisibleNodes.map(v => 
            getInvisibleChildren(v)).flat();
        const invisibleIndices = invisibleNodes.map(v => v.key)
            .concat(invisibleChildren);
        return visibleNodes.filter(v => !invisibleIndices.includes(v.key));
    }

    getVisibleEdges(visibleNodes) {
        const {nodes, links} = this.props;
        const nodeMap = new Map(nodes.map(v => [v.key, v]));
        const visibleIndices = visibleNodes.map(v => v.key);
        
        // check the parent nodes
        // returns the node itself if it's already in the visible nodes
        const getLowestParent = (v) => {
            while(!visibleIndices.includes(v)) {
                var node = nodeMap.get(v);
                if(node.parent !== null) {
                    v = node.parent;
                } else {
                    return -1;
                }
            }
            return v;
        }

        // an edge is visible for the following cases:
        // 1) both source and target are visible
        const visibleLinks = links.filter(e => 
            visibleIndices.includes(e.source) && visibleIndices.includes(e.target));
        // 2) some of the vertices are invisible, but their parents are visible
        const invisibleLinks = links.filter(e =>
            !visibleIndices.includes(e.source) || !visibleIndices.includes(e.target));
        const visibleParentLinks = invisibleLinks.reduce((acc, e) => {
            const src = getLowestParent(e.source);
            const dst = getLowestParent(e.target);
            if(src === -1 || dst === -1 || dst === src) {
                return acc;
            } else {
                return acc.concat({source: src, target: dst});
            }
        }, []);

        return visibleLinks.concat(visibleParentLinks);
    }

    renderChart() {
        const {changeChildrenVisibility} = this.props;
        const oldNodes = this.rect.data().concat(this.ellipse.data());
        const old = new Map(oldNodes.map(d => [d.key, d]));
        const visibleNodes = this.getVisibleNodes()
            .map(d => Object.assign(old.get(d.key) || {}, d));
        const visibleLinks = this.getVisibleEdges(visibleNodes)
            .map(d => Object.assign({}, d));

        // console.log(visibleNodes);
        // console.log(visibleLinks);
        
        // this.node = this.node
        const visibleEndpoints = visibleNodes.filter(d => d.kind === "endpoint");
        const visibleFields = visibleNodes.filter(d => d.kind === "field");
        const textHalfLen = d => d.name.length * 3.5 + 20
        this.ellipse = this.ellipse
            .data(visibleFields, d => d.key)
            .join(
                function(enter) {
                    return enter.append("ellipse");
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .attr("rx", textHalfLen)
            .attr("ry", 15)
            .attr("fill", d => scale(d.key))
            .call(drag(force))
            .on("click", (_, d) => changeChildrenVisibility({children: d.children}));

        this.rect = this.rect
            .data(visibleEndpoints, d => d.key)
            .join(
                function(enter) {
                    return enter.append("rect");
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .attr("width", d => 2 * textHalfLen(d))
            .attr("height", 30)
            .attr("fill", d => scale(d.key))
            .call(drag(force))
            .on("click", (_, d) => changeChildrenVisibility({children: d.children}));
        
        this.text = this.text
            .data(visibleNodes, d => d.key)
            .join(
                function(enter) {
                    return enter.append("text")
                        .text(d => d.name);
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .call(drag(force))
            .on("click", (_, d) => changeChildrenVisibility({children: d.children}));

        this.link = this.link
            .data(visibleLinks, d => [d.source, d.target])
            .join(
                function(enter) {
                    return enter.append("path")
                        //attach the arrow from defs;
                        .attr('marker-start', (d) => "url(#arrow)"); 
                },
                function(update) {
                    return update;
                },
                function(exit) {
                    return exit.remove();
                }
            )
            .attr("stroke-width", 2);

        force.nodes(visibleNodes);
        force.force("link").links(visibleLinks).id(d => d.key)
        // start force calculations after
        // React has taken care of enter/exit of elements
        
        force.on("tick", () => {
            this.link
                .attr( "d", d => "M" 
                    + d.source.x + "," 
                    + d.source.y + ", "
                    + d.target.x + "," 
                    + d.target.y);
                // .attr("x1", d => d.source.x)
                // .attr("y1", d => d.source.y)
                // .attr("x2", d => d.target.x)
                // .attr("y2", d => d.target.y);
            this.text
                // for centralize the text
                .attr("x", d => d.x - d.name.length * 3.5)
                .attr("y", d => d.y + 5);

            this.ellipse
                .attr("cx", d => d.x)
                .attr("cy", d => d.y);

            this.rect
                .attr("x", d => d.x - this.rect.attr("width")/2 + 10)
                .attr("y", d => d.y - this.rect.attr("height")/2);
        });

        force.alpha(1).restart();
    }

    componentDidMount() {
        this.d3Graph = d3.select(ReactDOM.findDOMNode(this));
        // define arrows
        this.d3Graph.append("svg:defs").append("svg:marker")
            .attr("id", "arrow")
            .attr("fill", "#999")
            .attr("viewBox", "0 -5 10 10")
            .attr('refX', -75) //so that it comes towards the center.
            .attr("markerWidth", 5)
            .attr("markerHeight", 5)
            .attr("orient", "auto")
            .append("svg:path")
            .attr("d", "M0,-5L10,0L0,5");
        this.link = this.d3Graph.append("g")
            .attr("stroke", "#999")
            // .attr("stroke-opacity", 0.6)
            .selectAll("path");
        this.ellipse = this.d3Graph.append("g")
            .selectAll("ellipse");
        this.rect = this.d3Graph.append("g")
            .attr("stroke", "#fff")
            .attr("stroke-width", 1)
            .selectAll("rect");
        this.text = this.d3Graph.append("g")
            .attr("fill", "#fff")
            .selectAll("text");
        this.renderChart();
    }

    componentDidUpdate() {
        this.renderChart();
    }

    render() {
        return (
            <svg width={graphWidth} height={graphHeight}>
            </svg>
        );
    }
};

const mapStateToProps = (state) => {
    return {
        nodes: state.nodes,
        links: state.links,
    };
};

const mapDispatchToProps = (dispatch) => {
    return {
        changeChildrenVisibility: ({ children }) => dispatch(changeChildrenVisibility({ children })),
    };
};

export default connect(mapStateToProps, mapDispatchToProps)(CollapsibleGraph);