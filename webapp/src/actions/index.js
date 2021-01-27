import { log } from "../utilities/logger";
import * as Consts from "../constants/action-types"

function makeActionCreator(type, ...argNames) {
    return function (...args) {
        const action = { type }
        argNames.forEach((arg, index) => {
            action[arg] = args[index]
        })
		log.info(type, action)
        return action
    }
}

export const changeChildrenVisibility = 
    makeActionCreator(Consts.CHANGE_CHILDREN_VISIBILITY, "payload");

// export const changeChildrenVisibility = ({children}) => {

// };