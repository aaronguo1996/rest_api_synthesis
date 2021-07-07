import React from 'react';
import { connect } from 'react-redux';
import * as am4core from "@amcharts/amcharts4/core";
import * as am4plugins_forceDirected from "@amcharts/amcharts4/plugins/forceDirected"; 

import * as am4charts from "@amcharts/amcharts4/charts";

import am4themes_animated from "@amcharts/amcharts4/themes/animated";
import am4themes_kelly from "@amcharts/amcharts4/themes/kelly";

/* Chart code */
// Themes begin
am4core.useTheme(am4themes_kelly);
am4core.useTheme(am4themes_animated);
// Themes end


class CollapsibleForest extends React.Component {
    componentDidMount() {
        const {schemas} = this.props;
        let chart = am4core.create("chartdiv", am4plugins_forceDirected.ForceDirectedTree);
        // chart.legend = new am4charts.Legend();
        let networkSeries = chart.series.push(new am4plugins_forceDirected.ForceDirectedSeries());
        networkSeries.data = schemas;
        networkSeries.dataFields.linkWith = "linkWith";
        networkSeries.dataFields.name = "name";
        networkSeries.dataFields.id = "name";
        networkSeries.dataFields.value = "value";
        networkSeries.dataFields.children = "children";

        // networkSeries.nodes.template.t
        networkSeries.nodes.template.expandAll = false;
        networkSeries.nodes.template.tooltipText = "{name}";
        networkSeries.nodes.template.fillOpacity = 1;

        networkSeries.nodes.template.label.text = "{name}"
        networkSeries.fontSize = 10;
        networkSeries.maxLevels = 1;
        networkSeries.maxRadius = am4core.percent(10);
        networkSeries.maxRadius = am4core.percent(6);
        networkSeries.manyBodyStrength = -10;
        networkSeries.nodes.template.label.hideOversized = false;
        networkSeries.nodes.template.label.truncate = false;

        this.chart = chart;
    }

    componentWillUnmount() {
        if (this.chart) {
          this.chart.dispose();
        }
      }

    render() {
        return (
            <div id="chartdiv"
                style={{ width: "100%", height: "500px" }}></div>
        )
    }
}




const mapStateToProps = (state) => {
    return {
        schemas: state.schemas,
    };
};

// const mapDispatchToProps = (dispatch) => {
//     return {
//         changeChildrenVisibility: ({ children }) => dispatch(changeChildrenVisibility({ children })),
//     };
// };

export default connect(mapStateToProps)(CollapsibleForest);