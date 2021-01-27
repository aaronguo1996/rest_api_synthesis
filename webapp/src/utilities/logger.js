import createLog from 'localstorage-logger';

export const log = createLog({
  logName: 'synthesis-log',
  maxLogSizeInBytes: 5 * 1024 * 1024 // 5MB
});